%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:08 EST 2020

% Result     : Theorem 5.43s
% Output     : Refutation 5.43s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 289 expanded)
%              Number of leaves         :   36 ( 117 expanded)
%              Depth                    :   10
%              Number of atoms          :  422 ( 793 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4306,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f84,f89,f133,f139,f195,f202,f233,f237,f733,f773,f806,f1885,f1914,f2360,f3446,f4259,f4305])).

fof(f4305,plain,(
    spl3_161 ),
    inference(avatar_contradiction_clause,[],[f4304])).

fof(f4304,plain,
    ( $false
    | spl3_161 ),
    inference(subsumption_resolution,[],[f4294,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f4294,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl3_161 ),
    inference(resolution,[],[f4258,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f4258,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | spl3_161 ),
    inference(avatar_component_clause,[],[f4256])).

fof(f4256,plain,
    ( spl3_161
  <=> r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_161])])).

fof(f4259,plain,
    ( ~ spl3_161
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_61
    | spl3_101 ),
    inference(avatar_split_clause,[],[f4254,f2357,f770,f74,f64,f4256])).

fof(f64,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f74,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f770,plain,
    ( spl3_61
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f2357,plain,
    ( spl3_101
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).

fof(f4254,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_61
    | spl3_101 ),
    inference(subsumption_resolution,[],[f4253,f76])).

fof(f76,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f4253,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | ~ spl3_61
    | spl3_101 ),
    inference(subsumption_resolution,[],[f4252,f66])).

fof(f66,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f4252,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_61
    | spl3_101 ),
    inference(subsumption_resolution,[],[f4240,f771])).

fof(f771,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f770])).

fof(f4240,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_101 ),
    inference(resolution,[],[f2359,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f2359,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_101 ),
    inference(avatar_component_clause,[],[f2357])).

fof(f3446,plain,
    ( ~ spl3_18
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f3445,f69,f64,f59,f173])).

fof(f173,plain,
    ( spl3_18
  <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f59,plain,
    ( spl3_1
  <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f69,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f3445,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f3444,f71])).

fof(f71,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f3444,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f3430,f66])).

fof(f3430,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(superposition,[],[f61,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f61,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f2360,plain,
    ( ~ spl3_101
    | spl3_56 ),
    inference(avatar_split_clause,[],[f2347,f612,f2357])).

fof(f612,plain,
    ( spl3_56
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f2347,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_56 ),
    inference(resolution,[],[f614,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f614,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_56 ),
    inference(avatar_component_clause,[],[f612])).

fof(f1914,plain,
    ( ~ spl3_56
    | ~ spl3_57
    | spl3_22 ),
    inference(avatar_split_clause,[],[f1898,f204,f616,f612])).

fof(f616,plain,
    ( spl3_57
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f204,plain,
    ( spl3_22
  <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f1898,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_22 ),
    inference(resolution,[],[f206,f307])).

fof(f307,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f140,f52])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_subset_1(X1,X2,X0),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f53,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f206,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f204])).

fof(f1885,plain,
    ( ~ spl3_22
    | ~ spl3_15
    | ~ spl3_16
    | spl3_18 ),
    inference(avatar_split_clause,[],[f1884,f173,f162,f158,f204])).

fof(f158,plain,
    ( spl3_15
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f162,plain,
    ( spl3_16
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f1884,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_15
    | ~ spl3_16
    | spl3_18 ),
    inference(subsumption_resolution,[],[f1883,f159])).

fof(f159,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f158])).

fof(f1883,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_16
    | spl3_18 ),
    inference(subsumption_resolution,[],[f1868,f163])).

fof(f163,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f162])).

fof(f1868,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_18 ),
    inference(superposition,[],[f175,f52])).

fof(f175,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f173])).

fof(f806,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_61 ),
    inference(avatar_contradiction_clause,[],[f805])).

fof(f805,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_61 ),
    inference(subsumption_resolution,[],[f804,f71])).

fof(f804,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | spl3_61 ),
    inference(subsumption_resolution,[],[f802,f66])).

fof(f802,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_61 ),
    inference(resolution,[],[f772,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f53,f52])).

fof(f772,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_61 ),
    inference(avatar_component_clause,[],[f770])).

fof(f773,plain,
    ( ~ spl3_61
    | ~ spl3_3
    | ~ spl3_4
    | spl3_60 ),
    inference(avatar_split_clause,[],[f768,f730,f74,f69,f770])).

fof(f730,plain,
    ( spl3_60
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f768,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_4
    | spl3_60 ),
    inference(subsumption_resolution,[],[f767,f76])).

fof(f767,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_60 ),
    inference(subsumption_resolution,[],[f766,f71])).

fof(f766,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_60 ),
    inference(subsumption_resolution,[],[f765,f198])).

fof(f198,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(subsumption_resolution,[],[f197,f51])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f197,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | r1_tarski(X0,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f42,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f54,f55])).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f54,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f765,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_60 ),
    inference(resolution,[],[f732,f49])).

fof(f732,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_60 ),
    inference(avatar_component_clause,[],[f730])).

fof(f733,plain,
    ( ~ spl3_60
    | spl3_57 ),
    inference(avatar_split_clause,[],[f728,f616,f730])).

fof(f728,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_57 ),
    inference(resolution,[],[f618,f45])).

fof(f618,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_57 ),
    inference(avatar_component_clause,[],[f616])).

fof(f237,plain,
    ( ~ spl3_5
    | ~ spl3_11
    | spl3_26 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_11
    | spl3_26 ),
    inference(unit_resulting_resolution,[],[f83,f132,f232,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f232,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl3_26
  <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f132,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl3_11
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f83,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_5
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f233,plain,
    ( ~ spl3_26
    | spl3_16 ),
    inference(avatar_split_clause,[],[f228,f162,f230])).

fof(f228,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_16 ),
    inference(resolution,[],[f164,f45])).

fof(f164,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f162])).

fof(f202,plain,
    ( ~ spl3_6
    | ~ spl3_12
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_12
    | spl3_21 ),
    inference(unit_resulting_resolution,[],[f88,f138,f194,f41])).

fof(f194,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl3_21
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f138,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl3_12
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f88,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f195,plain,
    ( ~ spl3_21
    | spl3_15 ),
    inference(avatar_split_clause,[],[f190,f158,f192])).

fof(f190,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_15 ),
    inference(resolution,[],[f160,f45])).

fof(f160,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f158])).

fof(f139,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f134,f74,f69,f136])).

fof(f134,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f126,f76])).

fof(f126,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f50,f71])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f133,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f128,f74,f64,f130])).

fof(f128,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f125,f76])).

fof(f125,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f50,f66])).

fof(f89,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f79,f69,f86])).

fof(f79,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f44,f71])).

fof(f84,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f78,f64,f81])).

fof(f78,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f44,f66])).

fof(f77,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f37,f74])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f32,f31,f30])).

fof(f30,plain,
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

fof(f31,plain,
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

fof(f32,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

fof(f72,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f39,f64])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f40,f59])).

fof(f40,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:59:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (16427)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.49  % (16435)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (16429)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (16440)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (16442)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (16428)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (16446)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (16456)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (16430)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (16434)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (16451)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (16441)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (16431)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (16450)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (16452)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (16448)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (16433)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (16449)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (16437)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (16453)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (16432)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (16444)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (16436)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (16445)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (16447)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (16454)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.57  % (16455)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.57  % (16443)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.57  % (16438)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.58  % (16439)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 3.23/0.83  % (16451)Time limit reached!
% 3.23/0.83  % (16451)------------------------------
% 3.23/0.83  % (16451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.23/0.84  % (16429)Time limit reached!
% 3.23/0.84  % (16429)------------------------------
% 3.23/0.84  % (16429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.23/0.84  % (16429)Termination reason: Time limit
% 3.23/0.84  
% 3.23/0.84  % (16429)Memory used [KB]: 6652
% 3.23/0.84  % (16429)Time elapsed: 0.408 s
% 3.23/0.84  % (16429)------------------------------
% 3.23/0.84  % (16429)------------------------------
% 3.23/0.85  % (16451)Termination reason: Time limit
% 3.23/0.85  
% 3.23/0.85  % (16451)Memory used [KB]: 13304
% 3.23/0.85  % (16451)Time elapsed: 0.417 s
% 3.23/0.85  % (16451)------------------------------
% 3.23/0.85  % (16451)------------------------------
% 4.34/0.93  % (16433)Time limit reached!
% 4.34/0.93  % (16433)------------------------------
% 4.34/0.93  % (16433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.93  % (16433)Termination reason: Time limit
% 4.34/0.93  
% 4.34/0.93  % (16433)Memory used [KB]: 13432
% 4.34/0.93  % (16433)Time elapsed: 0.501 s
% 4.34/0.93  % (16433)------------------------------
% 4.34/0.93  % (16433)------------------------------
% 4.34/0.94  % (16456)Time limit reached!
% 4.34/0.94  % (16456)------------------------------
% 4.34/0.94  % (16456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.95  % (16441)Time limit reached!
% 4.34/0.95  % (16441)------------------------------
% 4.34/0.95  % (16441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.96  % (16456)Termination reason: Time limit
% 4.34/0.96  
% 4.34/0.96  % (16456)Memory used [KB]: 3070
% 4.34/0.96  % (16456)Time elapsed: 0.507 s
% 4.34/0.96  % (16456)------------------------------
% 4.34/0.96  % (16456)------------------------------
% 4.34/0.97  % (16441)Termination reason: Time limit
% 4.34/0.97  
% 4.34/0.97  % (16441)Memory used [KB]: 4989
% 4.34/0.97  % (16441)Time elapsed: 0.510 s
% 4.34/0.97  % (16441)------------------------------
% 4.34/0.97  % (16441)------------------------------
% 4.34/0.98  % (16457)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 4.34/1.00  % (16458)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.95/1.02  % (16459)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.95/1.04  % (16434)Time limit reached!
% 4.95/1.04  % (16434)------------------------------
% 4.95/1.04  % (16434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.95/1.04  % (16434)Termination reason: Time limit
% 4.95/1.04  
% 4.95/1.04  % (16434)Memory used [KB]: 6268
% 4.95/1.04  % (16434)Time elapsed: 0.614 s
% 4.95/1.04  % (16434)------------------------------
% 4.95/1.04  % (16434)------------------------------
% 4.95/1.04  % (16460)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 5.43/1.10  % (16448)Refutation found. Thanks to Tanya!
% 5.43/1.10  % SZS status Theorem for theBenchmark
% 5.43/1.10  % SZS output start Proof for theBenchmark
% 5.43/1.10  fof(f4306,plain,(
% 5.43/1.10    $false),
% 5.43/1.10    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f84,f89,f133,f139,f195,f202,f233,f237,f733,f773,f806,f1885,f1914,f2360,f3446,f4259,f4305])).
% 5.43/1.10  fof(f4305,plain,(
% 5.43/1.10    spl3_161),
% 5.43/1.10    inference(avatar_contradiction_clause,[],[f4304])).
% 5.43/1.10  fof(f4304,plain,(
% 5.43/1.10    $false | spl3_161),
% 5.43/1.10    inference(subsumption_resolution,[],[f4294,f56])).
% 5.43/1.10  fof(f56,plain,(
% 5.43/1.10    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 5.43/1.10    inference(equality_resolution,[],[f47])).
% 5.43/1.10  fof(f47,plain,(
% 5.43/1.10    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 5.43/1.10    inference(cnf_transformation,[],[f36])).
% 5.43/1.10  fof(f36,plain,(
% 5.43/1.10    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 5.43/1.10    inference(flattening,[],[f35])).
% 5.43/1.10  fof(f35,plain,(
% 5.43/1.10    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 5.43/1.10    inference(nnf_transformation,[],[f2])).
% 5.43/1.10  fof(f2,axiom,(
% 5.43/1.10    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 5.43/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 5.43/1.10  fof(f4294,plain,(
% 5.43/1.10    ~r1_tarski(sK2,sK2) | spl3_161),
% 5.43/1.10    inference(resolution,[],[f4258,f43])).
% 5.43/1.10  fof(f43,plain,(
% 5.43/1.10    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 5.43/1.10    inference(cnf_transformation,[],[f22])).
% 5.43/1.10  fof(f22,plain,(
% 5.43/1.10    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 5.43/1.10    inference(ennf_transformation,[],[f3])).
% 5.43/1.10  fof(f3,axiom,(
% 5.43/1.10    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 5.43/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 5.43/1.10  fof(f4258,plain,(
% 5.43/1.10    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | spl3_161),
% 5.43/1.10    inference(avatar_component_clause,[],[f4256])).
% 5.43/1.10  fof(f4256,plain,(
% 5.43/1.10    spl3_161 <=> r1_tarski(sK2,k2_xboole_0(sK1,sK2))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_161])])).
% 5.43/1.10  fof(f4259,plain,(
% 5.43/1.10    ~spl3_161 | ~spl3_2 | ~spl3_4 | ~spl3_61 | spl3_101),
% 5.43/1.10    inference(avatar_split_clause,[],[f4254,f2357,f770,f74,f64,f4256])).
% 5.43/1.10  fof(f64,plain,(
% 5.43/1.10    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 5.43/1.10  fof(f74,plain,(
% 5.43/1.10    spl3_4 <=> l1_pre_topc(sK0)),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 5.43/1.10  fof(f770,plain,(
% 5.43/1.10    spl3_61 <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 5.43/1.10  fof(f2357,plain,(
% 5.43/1.10    spl3_101 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).
% 5.43/1.10  fof(f4254,plain,(
% 5.43/1.10    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_4 | ~spl3_61 | spl3_101)),
% 5.43/1.10    inference(subsumption_resolution,[],[f4253,f76])).
% 5.43/1.10  fof(f76,plain,(
% 5.43/1.10    l1_pre_topc(sK0) | ~spl3_4),
% 5.43/1.10    inference(avatar_component_clause,[],[f74])).
% 5.43/1.10  fof(f4253,plain,(
% 5.43/1.10    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~l1_pre_topc(sK0) | (~spl3_2 | ~spl3_61 | spl3_101)),
% 5.43/1.10    inference(subsumption_resolution,[],[f4252,f66])).
% 5.43/1.10  fof(f66,plain,(
% 5.43/1.10    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 5.43/1.10    inference(avatar_component_clause,[],[f64])).
% 5.43/1.10  fof(f4252,plain,(
% 5.43/1.10    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_61 | spl3_101)),
% 5.43/1.10    inference(subsumption_resolution,[],[f4240,f771])).
% 5.43/1.10  fof(f771,plain,(
% 5.43/1.10    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_61),
% 5.43/1.10    inference(avatar_component_clause,[],[f770])).
% 5.43/1.10  fof(f4240,plain,(
% 5.43/1.10    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_101),
% 5.43/1.10    inference(resolution,[],[f2359,f49])).
% 5.43/1.10  fof(f49,plain,(
% 5.43/1.10    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.43/1.10    inference(cnf_transformation,[],[f24])).
% 5.43/1.10  fof(f24,plain,(
% 5.43/1.10    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.43/1.10    inference(flattening,[],[f23])).
% 5.43/1.10  fof(f23,plain,(
% 5.43/1.10    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.43/1.10    inference(ennf_transformation,[],[f14])).
% 5.43/1.10  fof(f14,axiom,(
% 5.43/1.10    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 5.43/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 5.43/1.10  fof(f2359,plain,(
% 5.43/1.10    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_101),
% 5.43/1.10    inference(avatar_component_clause,[],[f2357])).
% 5.43/1.10  fof(f3446,plain,(
% 5.43/1.10    ~spl3_18 | spl3_1 | ~spl3_2 | ~spl3_3),
% 5.43/1.10    inference(avatar_split_clause,[],[f3445,f69,f64,f59,f173])).
% 5.43/1.10  fof(f173,plain,(
% 5.43/1.10    spl3_18 <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 5.43/1.10  fof(f59,plain,(
% 5.43/1.10    spl3_1 <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 5.43/1.10  fof(f69,plain,(
% 5.43/1.10    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 5.43/1.10  fof(f3445,plain,(
% 5.43/1.10    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 5.43/1.10    inference(subsumption_resolution,[],[f3444,f71])).
% 5.43/1.10  fof(f71,plain,(
% 5.43/1.10    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 5.43/1.10    inference(avatar_component_clause,[],[f69])).
% 5.43/1.10  fof(f3444,plain,(
% 5.43/1.10    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_1 | ~spl3_2)),
% 5.43/1.10    inference(subsumption_resolution,[],[f3430,f66])).
% 5.43/1.10  fof(f3430,plain,(
% 5.43/1.10    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_1),
% 5.43/1.10    inference(superposition,[],[f61,f52])).
% 5.43/1.10  fof(f52,plain,(
% 5.43/1.10    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.43/1.10    inference(cnf_transformation,[],[f27])).
% 5.43/1.10  fof(f27,plain,(
% 5.43/1.10    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.43/1.10    inference(flattening,[],[f26])).
% 5.43/1.10  fof(f26,plain,(
% 5.43/1.10    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 5.43/1.10    inference(ennf_transformation,[],[f11])).
% 5.43/1.10  fof(f11,axiom,(
% 5.43/1.10    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 5.43/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 5.43/1.10  fof(f61,plain,(
% 5.43/1.10    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_1),
% 5.43/1.10    inference(avatar_component_clause,[],[f59])).
% 5.43/1.10  fof(f2360,plain,(
% 5.43/1.10    ~spl3_101 | spl3_56),
% 5.43/1.10    inference(avatar_split_clause,[],[f2347,f612,f2357])).
% 5.43/1.10  fof(f612,plain,(
% 5.43/1.10    spl3_56 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 5.43/1.10  fof(f2347,plain,(
% 5.43/1.10    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_56),
% 5.43/1.10    inference(resolution,[],[f614,f45])).
% 5.43/1.10  fof(f45,plain,(
% 5.43/1.10    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 5.43/1.10    inference(cnf_transformation,[],[f34])).
% 5.43/1.10  fof(f34,plain,(
% 5.43/1.10    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 5.43/1.10    inference(nnf_transformation,[],[f12])).
% 5.43/1.10  fof(f12,axiom,(
% 5.43/1.10    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 5.43/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 5.43/1.10  fof(f614,plain,(
% 5.43/1.10    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_56),
% 5.43/1.10    inference(avatar_component_clause,[],[f612])).
% 5.43/1.10  fof(f1914,plain,(
% 5.43/1.10    ~spl3_56 | ~spl3_57 | spl3_22),
% 5.43/1.10    inference(avatar_split_clause,[],[f1898,f204,f616,f612])).
% 5.43/1.10  fof(f616,plain,(
% 5.43/1.10    spl3_57 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 5.43/1.10  fof(f204,plain,(
% 5.43/1.10    spl3_22 <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 5.43/1.10  fof(f1898,plain,(
% 5.43/1.10    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_22),
% 5.43/1.10    inference(resolution,[],[f206,f307])).
% 5.43/1.10  fof(f307,plain,(
% 5.43/1.10    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 5.43/1.10    inference(duplicate_literal_removal,[],[f306])).
% 5.43/1.10  fof(f306,plain,(
% 5.43/1.10    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.43/1.10    inference(superposition,[],[f140,f52])).
% 5.43/1.10  fof(f140,plain,(
% 5.43/1.10    ( ! [X2,X0,X1] : (r1_tarski(k4_subset_1(X1,X2,X0),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 5.43/1.10    inference(resolution,[],[f53,f44])).
% 5.43/1.10  fof(f44,plain,(
% 5.43/1.10    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 5.43/1.10    inference(cnf_transformation,[],[f34])).
% 5.43/1.10  fof(f53,plain,(
% 5.43/1.10    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.43/1.10    inference(cnf_transformation,[],[f29])).
% 5.43/1.10  fof(f29,plain,(
% 5.43/1.10    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.43/1.10    inference(flattening,[],[f28])).
% 5.43/1.10  fof(f28,plain,(
% 5.43/1.10    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 5.43/1.10    inference(ennf_transformation,[],[f10])).
% 5.43/1.10  fof(f10,axiom,(
% 5.43/1.10    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 5.43/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 5.43/1.10  fof(f206,plain,(
% 5.43/1.10    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_22),
% 5.43/1.10    inference(avatar_component_clause,[],[f204])).
% 5.43/1.10  fof(f1885,plain,(
% 5.43/1.10    ~spl3_22 | ~spl3_15 | ~spl3_16 | spl3_18),
% 5.43/1.10    inference(avatar_split_clause,[],[f1884,f173,f162,f158,f204])).
% 5.43/1.10  fof(f158,plain,(
% 5.43/1.10    spl3_15 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 5.43/1.10  fof(f162,plain,(
% 5.43/1.10    spl3_16 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 5.43/1.10  fof(f1884,plain,(
% 5.43/1.10    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | (~spl3_15 | ~spl3_16 | spl3_18)),
% 5.43/1.10    inference(subsumption_resolution,[],[f1883,f159])).
% 5.43/1.10  fof(f159,plain,(
% 5.43/1.10    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_15),
% 5.43/1.10    inference(avatar_component_clause,[],[f158])).
% 5.43/1.10  fof(f1883,plain,(
% 5.43/1.10    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_16 | spl3_18)),
% 5.43/1.10    inference(subsumption_resolution,[],[f1868,f163])).
% 5.43/1.10  fof(f163,plain,(
% 5.43/1.10    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_16),
% 5.43/1.10    inference(avatar_component_clause,[],[f162])).
% 5.43/1.10  fof(f1868,plain,(
% 5.43/1.10    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_18),
% 5.43/1.10    inference(superposition,[],[f175,f52])).
% 5.43/1.10  fof(f175,plain,(
% 5.43/1.10    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_18),
% 5.43/1.10    inference(avatar_component_clause,[],[f173])).
% 5.43/1.10  fof(f806,plain,(
% 5.43/1.10    ~spl3_2 | ~spl3_3 | spl3_61),
% 5.43/1.10    inference(avatar_contradiction_clause,[],[f805])).
% 5.43/1.10  fof(f805,plain,(
% 5.43/1.10    $false | (~spl3_2 | ~spl3_3 | spl3_61)),
% 5.43/1.10    inference(subsumption_resolution,[],[f804,f71])).
% 5.43/1.10  fof(f804,plain,(
% 5.43/1.10    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | spl3_61)),
% 5.43/1.10    inference(subsumption_resolution,[],[f802,f66])).
% 5.43/1.10  fof(f802,plain,(
% 5.43/1.10    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_61),
% 5.43/1.10    inference(resolution,[],[f772,f156])).
% 5.43/1.10  fof(f156,plain,(
% 5.43/1.10    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.43/1.10    inference(duplicate_literal_removal,[],[f155])).
% 5.43/1.10  fof(f155,plain,(
% 5.43/1.10    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.43/1.10    inference(superposition,[],[f53,f52])).
% 5.43/1.10  fof(f772,plain,(
% 5.43/1.10    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_61),
% 5.43/1.10    inference(avatar_component_clause,[],[f770])).
% 5.43/1.10  fof(f773,plain,(
% 5.43/1.10    ~spl3_61 | ~spl3_3 | ~spl3_4 | spl3_60),
% 5.43/1.10    inference(avatar_split_clause,[],[f768,f730,f74,f69,f770])).
% 5.43/1.10  fof(f730,plain,(
% 5.43/1.10    spl3_60 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 5.43/1.10  fof(f768,plain,(
% 5.43/1.10    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_3 | ~spl3_4 | spl3_60)),
% 5.43/1.10    inference(subsumption_resolution,[],[f767,f76])).
% 5.43/1.10  fof(f767,plain,(
% 5.43/1.10    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_3 | spl3_60)),
% 5.43/1.10    inference(subsumption_resolution,[],[f766,f71])).
% 5.43/1.10  fof(f766,plain,(
% 5.43/1.10    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_60),
% 5.43/1.10    inference(subsumption_resolution,[],[f765,f198])).
% 5.43/1.10  fof(f198,plain,(
% 5.43/1.10    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 5.43/1.10    inference(subsumption_resolution,[],[f197,f51])).
% 5.43/1.10  fof(f51,plain,(
% 5.43/1.10    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 5.43/1.10    inference(cnf_transformation,[],[f5])).
% 5.43/1.10  fof(f5,axiom,(
% 5.43/1.10    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 5.43/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 5.43/1.10  fof(f197,plain,(
% 5.43/1.10    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X1) | r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 5.43/1.10    inference(superposition,[],[f42,f91])).
% 5.43/1.10  fof(f91,plain,(
% 5.43/1.10    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 5.43/1.10    inference(superposition,[],[f54,f55])).
% 5.43/1.10  fof(f55,plain,(
% 5.43/1.10    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 5.43/1.10    inference(cnf_transformation,[],[f17])).
% 5.43/1.10  fof(f17,plain,(
% 5.43/1.10    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 5.43/1.10    inference(rectify,[],[f1])).
% 5.43/1.10  fof(f1,axiom,(
% 5.43/1.10    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 5.43/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 5.43/1.10  fof(f54,plain,(
% 5.43/1.10    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 5.43/1.10    inference(cnf_transformation,[],[f7])).
% 5.43/1.10  fof(f7,axiom,(
% 5.43/1.10    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 5.43/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 5.43/1.10  fof(f42,plain,(
% 5.43/1.10    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 5.43/1.10    inference(cnf_transformation,[],[f21])).
% 5.43/1.10  fof(f21,plain,(
% 5.43/1.10    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 5.43/1.10    inference(ennf_transformation,[],[f6])).
% 5.43/1.10  fof(f6,axiom,(
% 5.43/1.10    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 5.43/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 5.43/1.10  fof(f765,plain,(
% 5.43/1.10    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_60),
% 5.43/1.10    inference(resolution,[],[f732,f49])).
% 5.43/1.10  fof(f732,plain,(
% 5.43/1.10    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_60),
% 5.43/1.10    inference(avatar_component_clause,[],[f730])).
% 5.43/1.10  fof(f733,plain,(
% 5.43/1.10    ~spl3_60 | spl3_57),
% 5.43/1.10    inference(avatar_split_clause,[],[f728,f616,f730])).
% 5.43/1.10  fof(f728,plain,(
% 5.43/1.10    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_57),
% 5.43/1.10    inference(resolution,[],[f618,f45])).
% 5.43/1.10  fof(f618,plain,(
% 5.43/1.10    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_57),
% 5.43/1.10    inference(avatar_component_clause,[],[f616])).
% 5.43/1.10  fof(f237,plain,(
% 5.43/1.10    ~spl3_5 | ~spl3_11 | spl3_26),
% 5.43/1.10    inference(avatar_contradiction_clause,[],[f236])).
% 5.43/1.10  fof(f236,plain,(
% 5.43/1.10    $false | (~spl3_5 | ~spl3_11 | spl3_26)),
% 5.43/1.10    inference(unit_resulting_resolution,[],[f83,f132,f232,f41])).
% 5.43/1.10  fof(f41,plain,(
% 5.43/1.10    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 5.43/1.10    inference(cnf_transformation,[],[f20])).
% 5.43/1.10  fof(f20,plain,(
% 5.43/1.10    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 5.43/1.10    inference(flattening,[],[f19])).
% 5.43/1.10  fof(f19,plain,(
% 5.43/1.10    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 5.43/1.10    inference(ennf_transformation,[],[f4])).
% 5.43/1.10  fof(f4,axiom,(
% 5.43/1.10    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 5.43/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 5.43/1.10  fof(f232,plain,(
% 5.43/1.10    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_26),
% 5.43/1.10    inference(avatar_component_clause,[],[f230])).
% 5.43/1.10  fof(f230,plain,(
% 5.43/1.10    spl3_26 <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 5.43/1.10  fof(f132,plain,(
% 5.43/1.10    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl3_11),
% 5.43/1.10    inference(avatar_component_clause,[],[f130])).
% 5.43/1.10  fof(f130,plain,(
% 5.43/1.10    spl3_11 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 5.43/1.10  fof(f83,plain,(
% 5.43/1.10    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_5),
% 5.43/1.10    inference(avatar_component_clause,[],[f81])).
% 5.43/1.10  fof(f81,plain,(
% 5.43/1.10    spl3_5 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 5.43/1.10  fof(f233,plain,(
% 5.43/1.10    ~spl3_26 | spl3_16),
% 5.43/1.10    inference(avatar_split_clause,[],[f228,f162,f230])).
% 5.43/1.10  fof(f228,plain,(
% 5.43/1.10    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_16),
% 5.43/1.10    inference(resolution,[],[f164,f45])).
% 5.43/1.10  fof(f164,plain,(
% 5.43/1.10    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_16),
% 5.43/1.10    inference(avatar_component_clause,[],[f162])).
% 5.43/1.10  fof(f202,plain,(
% 5.43/1.10    ~spl3_6 | ~spl3_12 | spl3_21),
% 5.43/1.10    inference(avatar_contradiction_clause,[],[f201])).
% 5.43/1.10  fof(f201,plain,(
% 5.43/1.10    $false | (~spl3_6 | ~spl3_12 | spl3_21)),
% 5.43/1.10    inference(unit_resulting_resolution,[],[f88,f138,f194,f41])).
% 5.43/1.10  fof(f194,plain,(
% 5.43/1.10    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_21),
% 5.43/1.10    inference(avatar_component_clause,[],[f192])).
% 5.43/1.10  fof(f192,plain,(
% 5.43/1.10    spl3_21 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 5.43/1.10  fof(f138,plain,(
% 5.43/1.10    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_12),
% 5.43/1.10    inference(avatar_component_clause,[],[f136])).
% 5.43/1.10  fof(f136,plain,(
% 5.43/1.10    spl3_12 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 5.43/1.10  fof(f88,plain,(
% 5.43/1.10    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 5.43/1.10    inference(avatar_component_clause,[],[f86])).
% 5.43/1.10  fof(f86,plain,(
% 5.43/1.10    spl3_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 5.43/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 5.43/1.10  fof(f195,plain,(
% 5.43/1.10    ~spl3_21 | spl3_15),
% 5.43/1.10    inference(avatar_split_clause,[],[f190,f158,f192])).
% 5.43/1.10  fof(f190,plain,(
% 5.43/1.10    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_15),
% 5.43/1.10    inference(resolution,[],[f160,f45])).
% 5.43/1.10  fof(f160,plain,(
% 5.43/1.10    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_15),
% 5.43/1.10    inference(avatar_component_clause,[],[f158])).
% 5.43/1.10  fof(f139,plain,(
% 5.43/1.10    spl3_12 | ~spl3_3 | ~spl3_4),
% 5.43/1.10    inference(avatar_split_clause,[],[f134,f74,f69,f136])).
% 5.43/1.10  fof(f134,plain,(
% 5.43/1.10    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_4)),
% 5.43/1.10    inference(subsumption_resolution,[],[f126,f76])).
% 5.43/1.10  fof(f126,plain,(
% 5.43/1.10    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 5.43/1.10    inference(resolution,[],[f50,f71])).
% 5.43/1.10  fof(f50,plain,(
% 5.43/1.10    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 5.43/1.10    inference(cnf_transformation,[],[f25])).
% 5.43/1.10  fof(f25,plain,(
% 5.43/1.10    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.43/1.10    inference(ennf_transformation,[],[f13])).
% 5.43/1.10  fof(f13,axiom,(
% 5.43/1.10    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 5.43/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 5.43/1.10  fof(f133,plain,(
% 5.43/1.10    spl3_11 | ~spl3_2 | ~spl3_4),
% 5.43/1.10    inference(avatar_split_clause,[],[f128,f74,f64,f130])).
% 5.43/1.10  fof(f128,plain,(
% 5.43/1.10    r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl3_2 | ~spl3_4)),
% 5.43/1.10    inference(subsumption_resolution,[],[f125,f76])).
% 5.43/1.10  fof(f125,plain,(
% 5.43/1.10    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0) | ~spl3_2),
% 5.43/1.10    inference(resolution,[],[f50,f66])).
% 5.43/1.10  fof(f89,plain,(
% 5.43/1.10    spl3_6 | ~spl3_3),
% 5.43/1.10    inference(avatar_split_clause,[],[f79,f69,f86])).
% 5.43/1.10  fof(f79,plain,(
% 5.43/1.10    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 5.43/1.10    inference(resolution,[],[f44,f71])).
% 5.43/1.10  fof(f84,plain,(
% 5.43/1.10    spl3_5 | ~spl3_2),
% 5.43/1.10    inference(avatar_split_clause,[],[f78,f64,f81])).
% 5.43/1.12  fof(f78,plain,(
% 5.43/1.12    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_2),
% 5.43/1.12    inference(resolution,[],[f44,f66])).
% 5.43/1.12  fof(f77,plain,(
% 5.43/1.12    spl3_4),
% 5.43/1.12    inference(avatar_split_clause,[],[f37,f74])).
% 5.43/1.12  fof(f37,plain,(
% 5.43/1.12    l1_pre_topc(sK0)),
% 5.43/1.12    inference(cnf_transformation,[],[f33])).
% 5.43/1.12  fof(f33,plain,(
% 5.43/1.12    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 5.43/1.12    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f32,f31,f30])).
% 5.43/1.12  fof(f30,plain,(
% 5.43/1.12    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 5.43/1.12    introduced(choice_axiom,[])).
% 5.43/1.12  fof(f31,plain,(
% 5.43/1.12    ? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 5.43/1.12    introduced(choice_axiom,[])).
% 5.43/1.12  fof(f32,plain,(
% 5.43/1.12    ? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 5.43/1.12    introduced(choice_axiom,[])).
% 5.43/1.12  fof(f18,plain,(
% 5.43/1.12    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 5.43/1.12    inference(ennf_transformation,[],[f16])).
% 5.43/1.12  fof(f16,negated_conjecture,(
% 5.43/1.12    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 5.43/1.12    inference(negated_conjecture,[],[f15])).
% 5.43/1.12  fof(f15,conjecture,(
% 5.43/1.12    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 5.43/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).
% 5.43/1.12  fof(f72,plain,(
% 5.43/1.12    spl3_3),
% 5.43/1.12    inference(avatar_split_clause,[],[f38,f69])).
% 5.43/1.12  fof(f38,plain,(
% 5.43/1.12    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.43/1.12    inference(cnf_transformation,[],[f33])).
% 5.43/1.12  fof(f67,plain,(
% 5.43/1.12    spl3_2),
% 5.43/1.12    inference(avatar_split_clause,[],[f39,f64])).
% 5.43/1.12  fof(f39,plain,(
% 5.43/1.12    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.43/1.12    inference(cnf_transformation,[],[f33])).
% 5.43/1.12  fof(f62,plain,(
% 5.43/1.12    ~spl3_1),
% 5.43/1.12    inference(avatar_split_clause,[],[f40,f59])).
% 5.43/1.12  fof(f40,plain,(
% 5.43/1.12    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 5.43/1.12    inference(cnf_transformation,[],[f33])).
% 5.43/1.12  % SZS output end Proof for theBenchmark
% 5.43/1.12  % (16448)------------------------------
% 5.43/1.12  % (16448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.43/1.12  % (16448)Termination reason: Refutation
% 5.43/1.12  
% 5.43/1.12  % (16448)Memory used [KB]: 9466
% 5.43/1.12  % (16448)Time elapsed: 0.674 s
% 5.43/1.12  % (16448)------------------------------
% 5.43/1.12  % (16448)------------------------------
% 5.43/1.13  % (16426)Success in time 0.76 s
%------------------------------------------------------------------------------
