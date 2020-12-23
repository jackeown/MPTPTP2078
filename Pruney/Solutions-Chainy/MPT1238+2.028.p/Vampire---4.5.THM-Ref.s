%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:08 EST 2020

% Result     : Theorem 4.46s
% Output     : Refutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 288 expanded)
%              Number of leaves         :   36 ( 117 expanded)
%              Depth                    :   10
%              Number of atoms          :  421 ( 792 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4169,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f83,f88,f132,f138,f194,f201,f232,f234,f716,f747,f761,f1447,f1463,f2309,f3345,f4131,f4168])).

fof(f4168,plain,(
    spl3_154 ),
    inference(avatar_contradiction_clause,[],[f4167])).

fof(f4167,plain,
    ( $false
    | spl3_154 ),
    inference(subsumption_resolution,[],[f4157,f55])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f4157,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl3_154 ),
    inference(resolution,[],[f4130,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f4130,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | spl3_154 ),
    inference(avatar_component_clause,[],[f4128])).

fof(f4128,plain,
    ( spl3_154
  <=> r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_154])])).

fof(f4131,plain,
    ( ~ spl3_154
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_61
    | spl3_101 ),
    inference(avatar_split_clause,[],[f4126,f2306,f744,f73,f63,f4128])).

fof(f63,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f73,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f744,plain,
    ( spl3_61
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f2306,plain,
    ( spl3_101
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).

fof(f4126,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_61
    | spl3_101 ),
    inference(subsumption_resolution,[],[f4125,f75])).

fof(f75,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f4125,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | ~ spl3_61
    | spl3_101 ),
    inference(subsumption_resolution,[],[f4124,f65])).

fof(f65,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f4124,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_61
    | spl3_101 ),
    inference(subsumption_resolution,[],[f4112,f745])).

fof(f745,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f744])).

fof(f4112,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_101 ),
    inference(resolution,[],[f2308,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f2308,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_101 ),
    inference(avatar_component_clause,[],[f2306])).

fof(f3345,plain,
    ( ~ spl3_18
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f3344,f68,f63,f58,f172])).

fof(f172,plain,
    ( spl3_18
  <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f58,plain,
    ( spl3_1
  <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f68,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f3344,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f3343,f70])).

fof(f70,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f3343,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f3329,f65])).

fof(f3329,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(superposition,[],[f60,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f60,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f2309,plain,
    ( ~ spl3_101
    | spl3_56 ),
    inference(avatar_split_clause,[],[f2296,f619,f2306])).

fof(f619,plain,
    ( spl3_56
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f2296,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_56 ),
    inference(resolution,[],[f621,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f621,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_56 ),
    inference(avatar_component_clause,[],[f619])).

fof(f1463,plain,
    ( ~ spl3_56
    | ~ spl3_57
    | spl3_22 ),
    inference(avatar_split_clause,[],[f1453,f203,f623,f619])).

fof(f623,plain,
    ( spl3_57
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f203,plain,
    ( spl3_22
  <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f1453,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_22 ),
    inference(resolution,[],[f205,f314])).

fof(f314,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f139,f51])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_subset_1(X1,X2,X0),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f52,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f205,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f203])).

fof(f1447,plain,
    ( ~ spl3_22
    | ~ spl3_15
    | ~ spl3_16
    | spl3_18 ),
    inference(avatar_split_clause,[],[f1446,f172,f161,f157,f203])).

fof(f157,plain,
    ( spl3_15
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f161,plain,
    ( spl3_16
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f1446,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_15
    | ~ spl3_16
    | spl3_18 ),
    inference(subsumption_resolution,[],[f1445,f158])).

fof(f158,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f157])).

fof(f1445,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_16
    | spl3_18 ),
    inference(subsumption_resolution,[],[f1440,f162])).

fof(f162,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f161])).

fof(f1440,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_18 ),
    inference(superposition,[],[f174,f51])).

fof(f174,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f172])).

fof(f761,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_61 ),
    inference(avatar_contradiction_clause,[],[f760])).

fof(f760,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_61 ),
    inference(subsumption_resolution,[],[f759,f70])).

fof(f759,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | spl3_61 ),
    inference(subsumption_resolution,[],[f757,f65])).

fof(f757,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_61 ),
    inference(resolution,[],[f746,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f52,f51])).

fof(f746,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_61 ),
    inference(avatar_component_clause,[],[f744])).

fof(f747,plain,
    ( ~ spl3_61
    | ~ spl3_3
    | ~ spl3_4
    | spl3_60 ),
    inference(avatar_split_clause,[],[f742,f713,f73,f68,f744])).

fof(f713,plain,
    ( spl3_60
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f742,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_4
    | spl3_60 ),
    inference(subsumption_resolution,[],[f741,f75])).

fof(f741,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_60 ),
    inference(subsumption_resolution,[],[f740,f70])).

fof(f740,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_60 ),
    inference(subsumption_resolution,[],[f739,f197])).

fof(f197,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(subsumption_resolution,[],[f196,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | r1_tarski(X0,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f41,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f53,f54])).

fof(f54,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f53,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f739,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_60 ),
    inference(resolution,[],[f715,f48])).

fof(f715,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_60 ),
    inference(avatar_component_clause,[],[f713])).

fof(f716,plain,
    ( ~ spl3_60
    | spl3_57 ),
    inference(avatar_split_clause,[],[f711,f623,f713])).

fof(f711,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_57 ),
    inference(resolution,[],[f625,f44])).

fof(f625,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))
    | spl3_57 ),
    inference(avatar_component_clause,[],[f623])).

fof(f234,plain,
    ( ~ spl3_5
    | ~ spl3_11
    | spl3_26 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_11
    | spl3_26 ),
    inference(unit_resulting_resolution,[],[f82,f131,f231,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f231,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl3_26
  <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f131,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl3_11
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f82,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_5
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f232,plain,
    ( ~ spl3_26
    | spl3_16 ),
    inference(avatar_split_clause,[],[f227,f161,f229])).

fof(f227,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl3_16 ),
    inference(resolution,[],[f163,f44])).

fof(f163,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f161])).

fof(f201,plain,
    ( ~ spl3_6
    | ~ spl3_12
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_12
    | spl3_21 ),
    inference(unit_resulting_resolution,[],[f87,f137,f193,f40])).

fof(f193,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl3_21
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f137,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_12
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f87,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f194,plain,
    ( ~ spl3_21
    | spl3_15 ),
    inference(avatar_split_clause,[],[f189,f157,f191])).

fof(f189,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_15 ),
    inference(resolution,[],[f159,f44])).

fof(f159,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f157])).

fof(f138,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f133,f73,f68,f135])).

fof(f133,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f125,f75])).

fof(f125,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f49,f70])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f132,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f127,f73,f63,f129])).

fof(f127,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f124,f75])).

fof(f124,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f49,f65])).

fof(f88,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f78,f68,f85])).

fof(f78,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f43,f70])).

fof(f83,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f77,f63,f80])).

fof(f77,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f43,f65])).

fof(f76,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f36,f73])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f31,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
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

fof(f31,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).

fof(f71,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f68])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f38,f63])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f39,f58])).

fof(f39,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:09:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (25919)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (25935)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (25911)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (25917)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (25914)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (25909)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (25927)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (25925)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (25931)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (25908)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (25923)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (25913)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (25926)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (25937)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (25910)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (25912)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (25916)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (25915)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.42/0.55  % (25934)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.42/0.55  % (25918)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.42/0.55  % (25929)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.42/0.55  % (25930)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.42/0.55  % (25933)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.42/0.55  % (25921)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.42/0.56  % (25922)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.42/0.56  % (25924)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.56  % (25928)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.42/0.56  % (25932)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.56/0.58  % (25936)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.56/0.58  % (25920)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 3.04/0.81  % (25932)Time limit reached!
% 3.04/0.81  % (25932)------------------------------
% 3.04/0.81  % (25932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.04/0.81  % (25932)Termination reason: Time limit
% 3.04/0.81  % (25932)Termination phase: Saturation
% 3.04/0.81  
% 3.04/0.81  % (25932)Memory used [KB]: 12281
% 3.04/0.81  % (25932)Time elapsed: 0.400 s
% 3.04/0.81  % (25932)------------------------------
% 3.04/0.81  % (25932)------------------------------
% 3.52/0.82  % (25910)Time limit reached!
% 3.52/0.82  % (25910)------------------------------
% 3.52/0.82  % (25910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.52/0.82  % (25910)Termination reason: Time limit
% 3.52/0.82  % (25910)Termination phase: Saturation
% 3.52/0.82  
% 3.52/0.82  % (25910)Memory used [KB]: 6524
% 3.52/0.82  % (25910)Time elapsed: 0.404 s
% 3.52/0.82  % (25910)------------------------------
% 3.52/0.82  % (25910)------------------------------
% 3.87/0.92  % (25922)Time limit reached!
% 3.87/0.92  % (25922)------------------------------
% 3.87/0.92  % (25922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.87/0.92  % (25937)Time limit reached!
% 3.87/0.92  % (25937)------------------------------
% 3.87/0.92  % (25937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.87/0.93  % (25937)Termination reason: Time limit
% 3.87/0.93  % (25937)Termination phase: Saturation
% 3.87/0.93  
% 3.87/0.93  % (25937)Memory used [KB]: 3070
% 3.87/0.93  % (25937)Time elapsed: 0.509 s
% 3.87/0.93  % (25937)------------------------------
% 3.87/0.93  % (25937)------------------------------
% 3.87/0.93  % (25914)Time limit reached!
% 3.87/0.93  % (25914)------------------------------
% 3.87/0.93  % (25914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.87/0.93  % (25914)Termination reason: Time limit
% 3.87/0.93  
% 3.87/0.93  % (25914)Memory used [KB]: 14072
% 3.87/0.93  % (25914)Time elapsed: 0.516 s
% 3.87/0.93  % (25914)------------------------------
% 3.87/0.93  % (25914)------------------------------
% 3.87/0.93  % (25922)Termination reason: Time limit
% 3.87/0.93  
% 3.87/0.93  % (25922)Memory used [KB]: 4989
% 3.87/0.93  % (25922)Time elapsed: 0.512 s
% 3.87/0.93  % (25922)------------------------------
% 3.87/0.93  % (25922)------------------------------
% 3.87/0.93  % (25974)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 4.46/0.95  % (25975)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.46/0.96  % (25929)Refutation found. Thanks to Tanya!
% 4.46/0.96  % SZS status Theorem for theBenchmark
% 4.46/0.96  % SZS output start Proof for theBenchmark
% 4.46/0.96  fof(f4169,plain,(
% 4.46/0.96    $false),
% 4.46/0.96    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f83,f88,f132,f138,f194,f201,f232,f234,f716,f747,f761,f1447,f1463,f2309,f3345,f4131,f4168])).
% 4.46/0.96  fof(f4168,plain,(
% 4.46/0.96    spl3_154),
% 4.46/0.96    inference(avatar_contradiction_clause,[],[f4167])).
% 4.46/0.96  fof(f4167,plain,(
% 4.46/0.96    $false | spl3_154),
% 4.46/0.96    inference(subsumption_resolution,[],[f4157,f55])).
% 4.46/0.96  fof(f55,plain,(
% 4.46/0.96    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.46/0.96    inference(equality_resolution,[],[f46])).
% 4.46/0.96  fof(f46,plain,(
% 4.46/0.96    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.46/0.96    inference(cnf_transformation,[],[f35])).
% 4.46/0.96  fof(f35,plain,(
% 4.46/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.46/0.96    inference(flattening,[],[f34])).
% 4.46/0.96  fof(f34,plain,(
% 4.46/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.46/0.96    inference(nnf_transformation,[],[f1])).
% 4.46/0.96  fof(f1,axiom,(
% 4.46/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.46/0.96  fof(f4157,plain,(
% 4.46/0.96    ~r1_tarski(sK2,sK2) | spl3_154),
% 4.46/0.96    inference(resolution,[],[f4130,f42])).
% 4.46/0.96  fof(f42,plain,(
% 4.46/0.96    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 4.46/0.96    inference(cnf_transformation,[],[f21])).
% 4.46/0.96  fof(f21,plain,(
% 4.46/0.96    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 4.46/0.96    inference(ennf_transformation,[],[f2])).
% 4.46/0.96  fof(f2,axiom,(
% 4.46/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 4.46/0.96  fof(f4130,plain,(
% 4.46/0.96    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | spl3_154),
% 4.46/0.96    inference(avatar_component_clause,[],[f4128])).
% 4.46/0.96  fof(f4128,plain,(
% 4.46/0.96    spl3_154 <=> r1_tarski(sK2,k2_xboole_0(sK1,sK2))),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl3_154])])).
% 4.46/0.96  fof(f4131,plain,(
% 4.46/0.96    ~spl3_154 | ~spl3_2 | ~spl3_4 | ~spl3_61 | spl3_101),
% 4.46/0.96    inference(avatar_split_clause,[],[f4126,f2306,f744,f73,f63,f4128])).
% 4.46/0.96  fof(f63,plain,(
% 4.46/0.96    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 4.46/0.96  fof(f73,plain,(
% 4.46/0.96    spl3_4 <=> l1_pre_topc(sK0)),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 4.46/0.96  fof(f744,plain,(
% 4.46/0.96    spl3_61 <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 4.46/0.96  fof(f2306,plain,(
% 4.46/0.96    spl3_101 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).
% 4.46/0.96  fof(f4126,plain,(
% 4.46/0.96    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_4 | ~spl3_61 | spl3_101)),
% 4.46/0.96    inference(subsumption_resolution,[],[f4125,f75])).
% 4.46/0.96  fof(f75,plain,(
% 4.46/0.96    l1_pre_topc(sK0) | ~spl3_4),
% 4.46/0.96    inference(avatar_component_clause,[],[f73])).
% 4.46/0.96  fof(f4125,plain,(
% 4.46/0.96    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~l1_pre_topc(sK0) | (~spl3_2 | ~spl3_61 | spl3_101)),
% 4.46/0.96    inference(subsumption_resolution,[],[f4124,f65])).
% 4.46/0.96  fof(f65,plain,(
% 4.46/0.96    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 4.46/0.96    inference(avatar_component_clause,[],[f63])).
% 4.46/0.96  fof(f4124,plain,(
% 4.46/0.96    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_61 | spl3_101)),
% 4.46/0.96    inference(subsumption_resolution,[],[f4112,f745])).
% 4.46/0.96  fof(f745,plain,(
% 4.46/0.96    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_61),
% 4.46/0.96    inference(avatar_component_clause,[],[f744])).
% 4.46/0.96  fof(f4112,plain,(
% 4.46/0.96    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_101),
% 4.46/0.96    inference(resolution,[],[f2308,f48])).
% 4.46/0.96  fof(f48,plain,(
% 4.46/0.96    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.46/0.96    inference(cnf_transformation,[],[f23])).
% 4.46/0.96  fof(f23,plain,(
% 4.46/0.96    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.46/0.96    inference(flattening,[],[f22])).
% 4.46/0.96  fof(f22,plain,(
% 4.46/0.96    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.46/0.96    inference(ennf_transformation,[],[f14])).
% 4.46/0.96  fof(f14,axiom,(
% 4.46/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 4.46/0.96  fof(f2308,plain,(
% 4.46/0.96    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_101),
% 4.46/0.96    inference(avatar_component_clause,[],[f2306])).
% 4.46/0.96  fof(f3345,plain,(
% 4.46/0.96    ~spl3_18 | spl3_1 | ~spl3_2 | ~spl3_3),
% 4.46/0.96    inference(avatar_split_clause,[],[f3344,f68,f63,f58,f172])).
% 4.46/0.96  fof(f172,plain,(
% 4.46/0.96    spl3_18 <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 4.46/0.96  fof(f58,plain,(
% 4.46/0.96    spl3_1 <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 4.46/0.96  fof(f68,plain,(
% 4.46/0.96    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 4.46/0.96  fof(f3344,plain,(
% 4.46/0.96    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 4.46/0.96    inference(subsumption_resolution,[],[f3343,f70])).
% 4.46/0.96  fof(f70,plain,(
% 4.46/0.96    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 4.46/0.96    inference(avatar_component_clause,[],[f68])).
% 4.46/0.96  fof(f3343,plain,(
% 4.46/0.96    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_1 | ~spl3_2)),
% 4.46/0.96    inference(subsumption_resolution,[],[f3329,f65])).
% 4.46/0.96  fof(f3329,plain,(
% 4.46/0.96    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_1),
% 4.46/0.96    inference(superposition,[],[f60,f51])).
% 4.46/0.96  fof(f51,plain,(
% 4.46/0.96    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.46/0.96    inference(cnf_transformation,[],[f26])).
% 4.46/0.96  fof(f26,plain,(
% 4.46/0.96    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.46/0.96    inference(flattening,[],[f25])).
% 4.46/0.96  fof(f25,plain,(
% 4.46/0.96    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.46/0.96    inference(ennf_transformation,[],[f11])).
% 4.46/0.96  fof(f11,axiom,(
% 4.46/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 4.46/0.96  fof(f60,plain,(
% 4.46/0.96    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_1),
% 4.46/0.96    inference(avatar_component_clause,[],[f58])).
% 4.46/0.96  fof(f2309,plain,(
% 4.46/0.96    ~spl3_101 | spl3_56),
% 4.46/0.96    inference(avatar_split_clause,[],[f2296,f619,f2306])).
% 4.46/0.96  fof(f619,plain,(
% 4.46/0.96    spl3_56 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 4.46/0.96  fof(f2296,plain,(
% 4.46/0.96    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_56),
% 4.46/0.96    inference(resolution,[],[f621,f44])).
% 4.46/0.96  fof(f44,plain,(
% 4.46/0.96    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.46/0.96    inference(cnf_transformation,[],[f33])).
% 4.46/0.96  fof(f33,plain,(
% 4.46/0.96    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.46/0.96    inference(nnf_transformation,[],[f12])).
% 4.46/0.96  fof(f12,axiom,(
% 4.46/0.96    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 4.46/0.96  fof(f621,plain,(
% 4.46/0.96    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_56),
% 4.46/0.96    inference(avatar_component_clause,[],[f619])).
% 4.46/0.96  fof(f1463,plain,(
% 4.46/0.96    ~spl3_56 | ~spl3_57 | spl3_22),
% 4.46/0.96    inference(avatar_split_clause,[],[f1453,f203,f623,f619])).
% 4.46/0.96  fof(f623,plain,(
% 4.46/0.96    spl3_57 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 4.46/0.96  fof(f203,plain,(
% 4.46/0.96    spl3_22 <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 4.46/0.96  fof(f1453,plain,(
% 4.46/0.96    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_22),
% 4.46/0.96    inference(resolution,[],[f205,f314])).
% 4.46/0.96  fof(f314,plain,(
% 4.46/0.96    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.46/0.96    inference(duplicate_literal_removal,[],[f313])).
% 4.46/0.96  fof(f313,plain,(
% 4.46/0.96    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.46/0.96    inference(superposition,[],[f139,f51])).
% 4.46/0.96  fof(f139,plain,(
% 4.46/0.96    ( ! [X2,X0,X1] : (r1_tarski(k4_subset_1(X1,X2,X0),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.46/0.96    inference(resolution,[],[f52,f43])).
% 4.46/0.96  fof(f43,plain,(
% 4.46/0.96    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 4.46/0.96    inference(cnf_transformation,[],[f33])).
% 4.46/0.96  fof(f52,plain,(
% 4.46/0.96    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.46/0.96    inference(cnf_transformation,[],[f28])).
% 4.46/0.96  fof(f28,plain,(
% 4.46/0.96    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.46/0.96    inference(flattening,[],[f27])).
% 4.46/0.96  fof(f27,plain,(
% 4.46/0.96    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.46/0.96    inference(ennf_transformation,[],[f10])).
% 4.46/0.96  fof(f10,axiom,(
% 4.46/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 4.46/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 4.46/0.96  fof(f205,plain,(
% 4.46/0.96    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_22),
% 4.46/0.96    inference(avatar_component_clause,[],[f203])).
% 4.46/0.96  fof(f1447,plain,(
% 4.46/0.96    ~spl3_22 | ~spl3_15 | ~spl3_16 | spl3_18),
% 4.46/0.96    inference(avatar_split_clause,[],[f1446,f172,f161,f157,f203])).
% 4.46/0.96  fof(f157,plain,(
% 4.46/0.96    spl3_15 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 4.46/0.96  fof(f161,plain,(
% 4.46/0.96    spl3_16 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 4.46/0.96  fof(f1446,plain,(
% 4.46/0.96    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | (~spl3_15 | ~spl3_16 | spl3_18)),
% 4.46/0.96    inference(subsumption_resolution,[],[f1445,f158])).
% 4.46/0.96  fof(f158,plain,(
% 4.46/0.96    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_15),
% 4.46/0.96    inference(avatar_component_clause,[],[f157])).
% 4.46/0.96  fof(f1445,plain,(
% 4.46/0.96    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_16 | spl3_18)),
% 4.46/0.96    inference(subsumption_resolution,[],[f1440,f162])).
% 4.46/0.96  fof(f162,plain,(
% 4.46/0.96    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_16),
% 4.46/0.96    inference(avatar_component_clause,[],[f161])).
% 4.46/0.96  fof(f1440,plain,(
% 4.46/0.96    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_18),
% 4.46/0.96    inference(superposition,[],[f174,f51])).
% 4.46/0.96  fof(f174,plain,(
% 4.46/0.96    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_18),
% 4.46/0.96    inference(avatar_component_clause,[],[f172])).
% 4.46/0.96  fof(f761,plain,(
% 4.46/0.96    ~spl3_2 | ~spl3_3 | spl3_61),
% 4.46/0.96    inference(avatar_contradiction_clause,[],[f760])).
% 4.46/0.96  fof(f760,plain,(
% 4.46/0.96    $false | (~spl3_2 | ~spl3_3 | spl3_61)),
% 4.46/0.96    inference(subsumption_resolution,[],[f759,f70])).
% 4.46/0.96  fof(f759,plain,(
% 4.46/0.96    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | spl3_61)),
% 4.46/0.96    inference(subsumption_resolution,[],[f757,f65])).
% 4.46/0.96  fof(f757,plain,(
% 4.46/0.96    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_61),
% 4.46/0.96    inference(resolution,[],[f746,f155])).
% 4.46/0.96  fof(f155,plain,(
% 4.46/0.96    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.46/0.96    inference(duplicate_literal_removal,[],[f154])).
% 4.46/0.96  fof(f154,plain,(
% 4.46/0.96    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.46/0.96    inference(superposition,[],[f52,f51])).
% 4.46/0.96  fof(f746,plain,(
% 4.46/0.96    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_61),
% 4.46/0.96    inference(avatar_component_clause,[],[f744])).
% 4.46/0.96  fof(f747,plain,(
% 4.46/0.96    ~spl3_61 | ~spl3_3 | ~spl3_4 | spl3_60),
% 4.46/0.96    inference(avatar_split_clause,[],[f742,f713,f73,f68,f744])).
% 4.46/0.96  fof(f713,plain,(
% 4.46/0.96    spl3_60 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 4.46/0.96    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 4.46/0.96  fof(f742,plain,(
% 4.46/0.96    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_3 | ~spl3_4 | spl3_60)),
% 4.46/0.96    inference(subsumption_resolution,[],[f741,f75])).
% 4.46/0.96  fof(f741,plain,(
% 4.46/0.96    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_3 | spl3_60)),
% 4.46/0.96    inference(subsumption_resolution,[],[f740,f70])).
% 4.46/0.97  fof(f740,plain,(
% 4.46/0.97    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_60),
% 4.46/0.97    inference(subsumption_resolution,[],[f739,f197])).
% 4.46/0.97  fof(f197,plain,(
% 4.46/0.97    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.46/0.97    inference(subsumption_resolution,[],[f196,f50])).
% 4.46/0.97  fof(f50,plain,(
% 4.46/0.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.46/0.97    inference(cnf_transformation,[],[f5])).
% 4.46/0.97  fof(f5,axiom,(
% 4.46/0.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 4.46/0.97  fof(f196,plain,(
% 4.46/0.97    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X1) | r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.46/0.97    inference(superposition,[],[f41,f90])).
% 4.46/0.97  fof(f90,plain,(
% 4.46/0.97    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 4.46/0.97    inference(superposition,[],[f53,f54])).
% 4.46/0.97  fof(f54,plain,(
% 4.46/0.97    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.46/0.97    inference(cnf_transformation,[],[f3])).
% 4.46/0.97  fof(f3,axiom,(
% 4.46/0.97    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 4.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 4.46/0.97  fof(f53,plain,(
% 4.46/0.97    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.46/0.97    inference(cnf_transformation,[],[f7])).
% 4.46/0.97  fof(f7,axiom,(
% 4.46/0.97    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 4.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 4.46/0.97  fof(f41,plain,(
% 4.46/0.97    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 4.46/0.97    inference(cnf_transformation,[],[f20])).
% 4.46/0.97  fof(f20,plain,(
% 4.46/0.97    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 4.46/0.97    inference(ennf_transformation,[],[f6])).
% 4.46/0.97  fof(f6,axiom,(
% 4.46/0.97    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 4.46/0.97  fof(f739,plain,(
% 4.46/0.97    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_60),
% 4.46/0.97    inference(resolution,[],[f715,f48])).
% 4.46/0.97  fof(f715,plain,(
% 4.46/0.97    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_60),
% 4.46/0.97    inference(avatar_component_clause,[],[f713])).
% 4.46/0.97  fof(f716,plain,(
% 4.46/0.97    ~spl3_60 | spl3_57),
% 4.46/0.97    inference(avatar_split_clause,[],[f711,f623,f713])).
% 4.46/0.97  fof(f711,plain,(
% 4.46/0.97    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) | spl3_57),
% 4.46/0.97    inference(resolution,[],[f625,f44])).
% 4.46/0.97  fof(f625,plain,(
% 4.46/0.97    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) | spl3_57),
% 4.46/0.97    inference(avatar_component_clause,[],[f623])).
% 4.46/0.97  fof(f234,plain,(
% 4.46/0.97    ~spl3_5 | ~spl3_11 | spl3_26),
% 4.46/0.97    inference(avatar_contradiction_clause,[],[f233])).
% 4.46/0.97  fof(f233,plain,(
% 4.46/0.97    $false | (~spl3_5 | ~spl3_11 | spl3_26)),
% 4.46/0.97    inference(unit_resulting_resolution,[],[f82,f131,f231,f40])).
% 4.46/0.97  fof(f40,plain,(
% 4.46/0.97    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 4.46/0.97    inference(cnf_transformation,[],[f19])).
% 4.46/0.97  fof(f19,plain,(
% 4.46/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 4.46/0.97    inference(flattening,[],[f18])).
% 4.46/0.97  fof(f18,plain,(
% 4.46/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 4.46/0.97    inference(ennf_transformation,[],[f4])).
% 4.46/0.97  fof(f4,axiom,(
% 4.46/0.97    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 4.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 4.46/0.97  fof(f231,plain,(
% 4.46/0.97    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_26),
% 4.46/0.97    inference(avatar_component_clause,[],[f229])).
% 4.46/0.97  fof(f229,plain,(
% 4.46/0.97    spl3_26 <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))),
% 4.46/0.97    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 4.46/0.97  fof(f131,plain,(
% 4.46/0.97    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl3_11),
% 4.46/0.97    inference(avatar_component_clause,[],[f129])).
% 4.46/0.97  fof(f129,plain,(
% 4.46/0.97    spl3_11 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 4.46/0.97    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 4.46/0.97  fof(f82,plain,(
% 4.46/0.97    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_5),
% 4.46/0.97    inference(avatar_component_clause,[],[f80])).
% 4.46/0.97  fof(f80,plain,(
% 4.46/0.97    spl3_5 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 4.46/0.97    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 4.46/0.97  fof(f232,plain,(
% 4.46/0.97    ~spl3_26 | spl3_16),
% 4.46/0.97    inference(avatar_split_clause,[],[f227,f161,f229])).
% 4.46/0.97  fof(f227,plain,(
% 4.46/0.97    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl3_16),
% 4.46/0.97    inference(resolution,[],[f163,f44])).
% 4.46/0.97  fof(f163,plain,(
% 4.46/0.97    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_16),
% 4.46/0.97    inference(avatar_component_clause,[],[f161])).
% 4.46/0.97  fof(f201,plain,(
% 4.46/0.97    ~spl3_6 | ~spl3_12 | spl3_21),
% 4.46/0.97    inference(avatar_contradiction_clause,[],[f200])).
% 4.46/0.97  fof(f200,plain,(
% 4.46/0.97    $false | (~spl3_6 | ~spl3_12 | spl3_21)),
% 4.46/0.97    inference(unit_resulting_resolution,[],[f87,f137,f193,f40])).
% 4.46/0.97  fof(f193,plain,(
% 4.46/0.97    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_21),
% 4.46/0.97    inference(avatar_component_clause,[],[f191])).
% 4.46/0.97  fof(f191,plain,(
% 4.46/0.97    spl3_21 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 4.46/0.97    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 4.46/0.97  fof(f137,plain,(
% 4.46/0.97    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_12),
% 4.46/0.97    inference(avatar_component_clause,[],[f135])).
% 4.46/0.97  fof(f135,plain,(
% 4.46/0.97    spl3_12 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 4.46/0.97    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 4.46/0.97  fof(f87,plain,(
% 4.46/0.97    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 4.46/0.97    inference(avatar_component_clause,[],[f85])).
% 4.46/0.97  fof(f85,plain,(
% 4.46/0.97    spl3_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 4.46/0.97    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 4.46/0.97  fof(f194,plain,(
% 4.46/0.97    ~spl3_21 | spl3_15),
% 4.46/0.97    inference(avatar_split_clause,[],[f189,f157,f191])).
% 4.46/0.97  fof(f189,plain,(
% 4.46/0.97    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_15),
% 4.46/0.97    inference(resolution,[],[f159,f44])).
% 4.46/0.97  fof(f159,plain,(
% 4.46/0.97    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_15),
% 4.46/0.97    inference(avatar_component_clause,[],[f157])).
% 4.46/0.97  fof(f138,plain,(
% 4.46/0.97    spl3_12 | ~spl3_3 | ~spl3_4),
% 4.46/0.97    inference(avatar_split_clause,[],[f133,f73,f68,f135])).
% 4.46/0.97  fof(f133,plain,(
% 4.46/0.97    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_4)),
% 4.46/0.97    inference(subsumption_resolution,[],[f125,f75])).
% 4.46/0.97  fof(f125,plain,(
% 4.46/0.97    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 4.46/0.97    inference(resolution,[],[f49,f70])).
% 4.46/0.97  fof(f49,plain,(
% 4.46/0.97    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 4.46/0.97    inference(cnf_transformation,[],[f24])).
% 4.46/0.97  fof(f24,plain,(
% 4.46/0.97    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.46/0.97    inference(ennf_transformation,[],[f13])).
% 4.46/0.97  fof(f13,axiom,(
% 4.46/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 4.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 4.46/0.97  fof(f132,plain,(
% 4.46/0.97    spl3_11 | ~spl3_2 | ~spl3_4),
% 4.46/0.97    inference(avatar_split_clause,[],[f127,f73,f63,f129])).
% 4.46/0.97  fof(f127,plain,(
% 4.46/0.97    r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl3_2 | ~spl3_4)),
% 4.46/0.97    inference(subsumption_resolution,[],[f124,f75])).
% 4.46/0.97  fof(f124,plain,(
% 4.46/0.97    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0) | ~spl3_2),
% 4.46/0.97    inference(resolution,[],[f49,f65])).
% 4.46/0.97  fof(f88,plain,(
% 4.46/0.97    spl3_6 | ~spl3_3),
% 4.46/0.97    inference(avatar_split_clause,[],[f78,f68,f85])).
% 4.46/0.97  fof(f78,plain,(
% 4.46/0.97    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 4.46/0.97    inference(resolution,[],[f43,f70])).
% 4.46/0.97  fof(f83,plain,(
% 4.46/0.97    spl3_5 | ~spl3_2),
% 4.46/0.97    inference(avatar_split_clause,[],[f77,f63,f80])).
% 4.46/0.97  fof(f77,plain,(
% 4.46/0.97    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_2),
% 4.46/0.97    inference(resolution,[],[f43,f65])).
% 4.46/0.97  fof(f76,plain,(
% 4.46/0.97    spl3_4),
% 4.46/0.97    inference(avatar_split_clause,[],[f36,f73])).
% 4.46/0.97  fof(f36,plain,(
% 4.46/0.97    l1_pre_topc(sK0)),
% 4.46/0.97    inference(cnf_transformation,[],[f32])).
% 4.46/0.97  fof(f32,plain,(
% 4.46/0.97    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 4.46/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f31,f30,f29])).
% 4.46/0.97  fof(f29,plain,(
% 4.46/0.97    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 4.46/0.97    introduced(choice_axiom,[])).
% 4.46/0.97  fof(f30,plain,(
% 4.46/0.97    ? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.46/0.97    introduced(choice_axiom,[])).
% 4.46/0.97  fof(f31,plain,(
% 4.46/0.97    ? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.46/0.97    introduced(choice_axiom,[])).
% 4.46/0.97  fof(f17,plain,(
% 4.46/0.97    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.46/0.97    inference(ennf_transformation,[],[f16])).
% 4.46/0.97  fof(f16,negated_conjecture,(
% 4.46/0.97    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 4.46/0.97    inference(negated_conjecture,[],[f15])).
% 4.46/0.97  fof(f15,conjecture,(
% 4.46/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 4.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).
% 4.46/0.97  fof(f71,plain,(
% 4.46/0.97    spl3_3),
% 4.46/0.97    inference(avatar_split_clause,[],[f37,f68])).
% 4.46/0.97  fof(f37,plain,(
% 4.46/0.97    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.46/0.97    inference(cnf_transformation,[],[f32])).
% 4.46/0.97  fof(f66,plain,(
% 4.46/0.97    spl3_2),
% 4.46/0.97    inference(avatar_split_clause,[],[f38,f63])).
% 4.46/0.97  fof(f38,plain,(
% 4.46/0.97    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.46/0.97    inference(cnf_transformation,[],[f32])).
% 4.46/0.97  fof(f61,plain,(
% 4.46/0.97    ~spl3_1),
% 4.46/0.97    inference(avatar_split_clause,[],[f39,f58])).
% 4.46/0.97  fof(f39,plain,(
% 4.46/0.97    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 4.46/0.97    inference(cnf_transformation,[],[f32])).
% 4.46/0.97  % SZS output end Proof for theBenchmark
% 4.46/0.97  % (25929)------------------------------
% 4.46/0.97  % (25929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/0.97  % (25929)Termination reason: Refutation
% 4.46/0.97  
% 4.46/0.97  % (25929)Memory used [KB]: 9338
% 4.46/0.97  % (25929)Time elapsed: 0.549 s
% 4.46/0.97  % (25929)------------------------------
% 4.46/0.97  % (25929)------------------------------
% 4.46/0.97  % (25907)Success in time 0.604 s
%------------------------------------------------------------------------------
