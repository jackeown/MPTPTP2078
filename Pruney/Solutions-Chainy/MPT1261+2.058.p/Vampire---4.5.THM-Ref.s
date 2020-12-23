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
% DateTime   : Thu Dec  3 13:11:56 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 215 expanded)
%              Number of leaves         :   33 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  327 ( 702 expanded)
%              Number of equality atoms :   69 ( 153 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3905,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f105,f110,f115,f120,f132,f247,f405,f440,f698,f703,f715,f719,f780,f3892,f3903,f3904])).

fof(f3904,plain,
    ( k2_pre_topc(sK0,sK1) != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | sK1 != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3903,plain,
    ( k2_pre_topc(sK0,sK1) != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | sK1 != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3892,plain,
    ( spl2_191
    | ~ spl2_3
    | ~ spl2_26
    | ~ spl2_59 ),
    inference(avatar_split_clause,[],[f3891,f678,f402,f107,f3779])).

fof(f3779,plain,
    ( spl2_191
  <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_191])])).

fof(f107,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f402,plain,
    ( spl2_26
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f678,plain,
    ( spl2_59
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f3891,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_26
    | ~ spl2_59 ),
    inference(forward_demodulation,[],[f3710,f404])).

fof(f404,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f402])).

fof(f3710,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_59 ),
    inference(resolution,[],[f680,f351])).

fof(f351,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)) )
    | ~ spl2_3 ),
    inference(resolution,[],[f95,f109])).

fof(f109,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f83,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f680,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f678])).

fof(f780,plain,
    ( spl2_59
    | ~ spl2_46 ),
    inference(avatar_split_clause,[],[f774,f586,f678])).

fof(f586,plain,
    ( spl2_46
  <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f774,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_46 ),
    inference(resolution,[],[f588,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f588,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f586])).

fof(f719,plain,
    ( spl2_47
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f718,f566,f592])).

fof(f592,plain,
    ( spl2_47
  <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f566,plain,
    ( spl2_44
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f718,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f711,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f711,plain,
    ( sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_44 ),
    inference(resolution,[],[f568,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_tarski(X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f71,f68])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f568,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f566])).

fof(f715,plain,
    ( spl2_46
    | ~ spl2_6
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f707,f566,f128,f586])).

fof(f128,plain,
    ( spl2_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f707,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_6
    | ~ spl2_44 ),
    inference(unit_resulting_resolution,[],[f130,f568,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f130,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f703,plain,
    ( spl2_44
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f702,f107,f101,f566])).

fof(f101,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f702,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f542,f102])).

fof(f102,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f542,plain,
    ( ! [X4] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X4),sK1)
    | ~ spl2_3 ),
    inference(superposition,[],[f87,f306])).

fof(f306,plain,
    ( ! [X0] : k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f109,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f79,f84])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f70,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f65,f84])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f698,plain,
    ( spl2_44
    | ~ spl2_3
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f695,f112,f97,f107,f566])).

fof(f97,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f112,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f695,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f98,f289])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_tops_1(sK0,X0),X0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f64,f114])).

fof(f114,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f98,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f440,plain,
    ( spl2_30
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f428,f112,f107,f437])).

fof(f437,plain,
    ( spl2_30
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f428,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f114,f109,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f405,plain,
    ( spl2_26
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f393,f112,f107,f402])).

fof(f393,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f114,f109,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f247,plain,
    ( spl2_16
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f236,f117,f112,f107,f244])).

fof(f244,plain,
    ( spl2_16
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f117,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f236,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f119,f114,f109,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f119,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f132,plain,
    ( spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f126,f107,f128])).

fof(f126,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f77,f109])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f120,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f54,f117])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).

fof(f50,plain,
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

fof(f51,plain,
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

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f115,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f55,f112])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f110,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f56,f107])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f57,f101,f97])).

fof(f57,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f104,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f58,f101,f97])).

fof(f58,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:17:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (9086)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (9088)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (9098)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (9084)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (9096)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (9099)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (9089)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (9097)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (9094)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (9090)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (9087)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (9085)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (9093)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (9091)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (9100)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (9101)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.51  % (9095)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.51  % (9092)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.76/0.61  % (9090)Refutation found. Thanks to Tanya!
% 1.76/0.61  % SZS status Theorem for theBenchmark
% 1.76/0.62  % SZS output start Proof for theBenchmark
% 1.76/0.62  fof(f3905,plain,(
% 1.76/0.62    $false),
% 1.76/0.62    inference(avatar_sat_refutation,[],[f104,f105,f110,f115,f120,f132,f247,f405,f440,f698,f703,f715,f719,f780,f3892,f3903,f3904])).
% 1.76/0.62  fof(f3904,plain,(
% 1.76/0.62    k2_pre_topc(sK0,sK1) != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | sK1 != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.76/0.62    introduced(theory_tautology_sat_conflict,[])).
% 1.76/0.62  fof(f3903,plain,(
% 1.76/0.62    k2_pre_topc(sK0,sK1) != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | sK1 != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0) | ~v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 1.76/0.62    introduced(theory_tautology_sat_conflict,[])).
% 1.76/0.62  fof(f3892,plain,(
% 1.76/0.62    spl2_191 | ~spl2_3 | ~spl2_26 | ~spl2_59),
% 1.76/0.62    inference(avatar_split_clause,[],[f3891,f678,f402,f107,f3779])).
% 1.76/0.62  fof(f3779,plain,(
% 1.76/0.62    spl2_191 <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_191])])).
% 1.76/0.62  fof(f107,plain,(
% 1.76/0.62    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.76/0.62  fof(f402,plain,(
% 1.76/0.62    spl2_26 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 1.76/0.62  fof(f678,plain,(
% 1.76/0.62    spl2_59 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 1.76/0.62  fof(f3891,plain,(
% 1.76/0.62    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_26 | ~spl2_59)),
% 1.76/0.62    inference(forward_demodulation,[],[f3710,f404])).
% 1.76/0.62  fof(f404,plain,(
% 1.76/0.62    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_26),
% 1.76/0.62    inference(avatar_component_clause,[],[f402])).
% 1.76/0.62  fof(f3710,plain,(
% 1.76/0.62    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_59)),
% 1.76/0.62    inference(resolution,[],[f680,f351])).
% 1.76/0.62  fof(f351,plain,(
% 1.76/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))) ) | ~spl2_3),
% 1.76/0.62    inference(resolution,[],[f95,f109])).
% 1.76/0.62  fof(f109,plain,(
% 1.76/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.76/0.62    inference(avatar_component_clause,[],[f107])).
% 1.76/0.62  fof(f95,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))) )),
% 1.76/0.62    inference(definition_unfolding,[],[f83,f68])).
% 1.76/0.62  fof(f68,plain,(
% 1.76/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f12])).
% 1.76/0.62  fof(f12,axiom,(
% 1.76/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.76/0.62  fof(f83,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f47])).
% 1.76/0.62  fof(f47,plain,(
% 1.76/0.62    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.76/0.62    inference(flattening,[],[f46])).
% 1.76/0.62  fof(f46,plain,(
% 1.76/0.62    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.76/0.62    inference(ennf_transformation,[],[f16])).
% 1.76/0.62  fof(f16,axiom,(
% 1.76/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.76/0.62  fof(f680,plain,(
% 1.76/0.62    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_59),
% 1.76/0.62    inference(avatar_component_clause,[],[f678])).
% 1.76/0.62  fof(f780,plain,(
% 1.76/0.62    spl2_59 | ~spl2_46),
% 1.76/0.62    inference(avatar_split_clause,[],[f774,f586,f678])).
% 1.76/0.62  fof(f586,plain,(
% 1.76/0.62    spl2_46 <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 1.76/0.62  fof(f774,plain,(
% 1.76/0.62    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_46),
% 1.76/0.62    inference(resolution,[],[f588,f78])).
% 1.76/0.62  fof(f78,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f53])).
% 1.76/0.62  fof(f53,plain,(
% 1.76/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.76/0.62    inference(nnf_transformation,[],[f19])).
% 1.76/0.62  fof(f19,axiom,(
% 1.76/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.76/0.62  fof(f588,plain,(
% 1.76/0.62    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl2_46),
% 1.76/0.62    inference(avatar_component_clause,[],[f586])).
% 1.76/0.62  fof(f719,plain,(
% 1.76/0.62    spl2_47 | ~spl2_44),
% 1.76/0.62    inference(avatar_split_clause,[],[f718,f566,f592])).
% 1.76/0.62  fof(f592,plain,(
% 1.76/0.62    spl2_47 <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 1.76/0.62  fof(f566,plain,(
% 1.76/0.62    spl2_44 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 1.76/0.62  fof(f718,plain,(
% 1.76/0.62    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_44),
% 1.76/0.62    inference(forward_demodulation,[],[f711,f66])).
% 1.76/0.62  fof(f66,plain,(
% 1.76/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f11])).
% 1.76/0.62  fof(f11,axiom,(
% 1.76/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.76/0.62  fof(f711,plain,(
% 1.76/0.62    sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | ~spl2_44),
% 1.76/0.62    inference(resolution,[],[f568,f89])).
% 1.76/0.62  fof(f89,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1) )),
% 1.76/0.62    inference(definition_unfolding,[],[f71,f68])).
% 1.76/0.62  fof(f71,plain,(
% 1.76/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f34])).
% 1.76/0.62  fof(f34,plain,(
% 1.76/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.76/0.62    inference(ennf_transformation,[],[f2])).
% 1.76/0.62  fof(f2,axiom,(
% 1.76/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.76/0.62  fof(f568,plain,(
% 1.76/0.62    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_44),
% 1.76/0.62    inference(avatar_component_clause,[],[f566])).
% 1.76/0.62  fof(f715,plain,(
% 1.76/0.62    spl2_46 | ~spl2_6 | ~spl2_44),
% 1.76/0.62    inference(avatar_split_clause,[],[f707,f566,f128,f586])).
% 1.76/0.62  fof(f128,plain,(
% 1.76/0.62    spl2_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.76/0.62  fof(f707,plain,(
% 1.76/0.62    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_6 | ~spl2_44)),
% 1.76/0.62    inference(unit_resulting_resolution,[],[f130,f568,f82])).
% 1.76/0.62  fof(f82,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f45])).
% 1.76/0.62  fof(f45,plain,(
% 1.76/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.76/0.62    inference(flattening,[],[f44])).
% 1.76/0.62  fof(f44,plain,(
% 1.76/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.76/0.62    inference(ennf_transformation,[],[f3])).
% 1.76/0.62  fof(f3,axiom,(
% 1.76/0.62    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.76/0.62  fof(f130,plain,(
% 1.76/0.62    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_6),
% 1.76/0.62    inference(avatar_component_clause,[],[f128])).
% 1.76/0.62  fof(f703,plain,(
% 1.76/0.62    spl2_44 | ~spl2_2 | ~spl2_3),
% 1.76/0.62    inference(avatar_split_clause,[],[f702,f107,f101,f566])).
% 1.76/0.62  fof(f101,plain,(
% 1.76/0.62    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.76/0.62  fof(f702,plain,(
% 1.76/0.62    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3)),
% 1.76/0.62    inference(superposition,[],[f542,f102])).
% 1.76/0.62  fof(f102,plain,(
% 1.76/0.62    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 1.76/0.62    inference(avatar_component_clause,[],[f101])).
% 1.76/0.62  fof(f542,plain,(
% 1.76/0.62    ( ! [X4] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X4),sK1)) ) | ~spl2_3),
% 1.76/0.62    inference(superposition,[],[f87,f306])).
% 1.76/0.62  fof(f306,plain,(
% 1.76/0.62    ( ! [X0] : (k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_3),
% 1.76/0.62    inference(unit_resulting_resolution,[],[f109,f92])).
% 1.76/0.62  fof(f92,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 1.76/0.62    inference(definition_unfolding,[],[f79,f84])).
% 1.76/0.62  fof(f84,plain,(
% 1.76/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.76/0.62    inference(definition_unfolding,[],[f70,f67])).
% 1.76/0.62  fof(f67,plain,(
% 1.76/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f18])).
% 1.76/0.62  fof(f18,axiom,(
% 1.76/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.76/0.62  fof(f70,plain,(
% 1.76/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f1])).
% 1.76/0.62  fof(f1,axiom,(
% 1.76/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.76/0.62  fof(f79,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f41])).
% 1.76/0.62  fof(f41,plain,(
% 1.76/0.62    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.76/0.62    inference(ennf_transformation,[],[f17])).
% 1.76/0.62  fof(f17,axiom,(
% 1.76/0.62    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.76/0.62  fof(f87,plain,(
% 1.76/0.62    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 1.76/0.62    inference(definition_unfolding,[],[f65,f84])).
% 1.76/0.62  fof(f65,plain,(
% 1.76/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f5])).
% 1.76/0.62  fof(f5,axiom,(
% 1.76/0.62    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.76/0.62  fof(f698,plain,(
% 1.76/0.62    spl2_44 | ~spl2_3 | ~spl2_1 | ~spl2_4),
% 1.76/0.62    inference(avatar_split_clause,[],[f695,f112,f97,f107,f566])).
% 1.76/0.62  fof(f97,plain,(
% 1.76/0.62    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.76/0.62  fof(f112,plain,(
% 1.76/0.62    spl2_4 <=> l1_pre_topc(sK0)),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.76/0.62  fof(f695,plain,(
% 1.76/0.62    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_1 | ~spl2_4)),
% 1.76/0.62    inference(resolution,[],[f98,f289])).
% 1.76/0.62  fof(f289,plain,(
% 1.76/0.62    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_tops_1(sK0,X0),X0)) ) | ~spl2_4),
% 1.76/0.62    inference(resolution,[],[f64,f114])).
% 1.76/0.62  fof(f114,plain,(
% 1.76/0.62    l1_pre_topc(sK0) | ~spl2_4),
% 1.76/0.62    inference(avatar_component_clause,[],[f112])).
% 1.76/0.62  fof(f64,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f33])).
% 1.76/0.62  fof(f33,plain,(
% 1.76/0.62    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.76/0.62    inference(flattening,[],[f32])).
% 1.76/0.62  fof(f32,plain,(
% 1.76/0.62    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f24])).
% 1.76/0.62  fof(f24,axiom,(
% 1.76/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 1.76/0.62  fof(f98,plain,(
% 1.76/0.62    v4_pre_topc(sK1,sK0) | ~spl2_1),
% 1.76/0.62    inference(avatar_component_clause,[],[f97])).
% 1.76/0.62  fof(f440,plain,(
% 1.76/0.62    spl2_30 | ~spl2_3 | ~spl2_4),
% 1.76/0.62    inference(avatar_split_clause,[],[f428,f112,f107,f437])).
% 1.76/0.62  fof(f437,plain,(
% 1.76/0.62    spl2_30 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 1.76/0.62  fof(f428,plain,(
% 1.76/0.62    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 1.76/0.62    inference(unit_resulting_resolution,[],[f114,f109,f63])).
% 1.76/0.62  fof(f63,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f31])).
% 1.76/0.62  fof(f31,plain,(
% 1.76/0.62    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f21])).
% 1.76/0.62  fof(f21,axiom,(
% 1.76/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 1.76/0.62  fof(f405,plain,(
% 1.76/0.62    spl2_26 | ~spl2_3 | ~spl2_4),
% 1.76/0.62    inference(avatar_split_clause,[],[f393,f112,f107,f402])).
% 1.76/0.62  fof(f393,plain,(
% 1.76/0.62    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 1.76/0.62    inference(unit_resulting_resolution,[],[f114,f109,f62])).
% 1.76/0.62  fof(f62,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f30])).
% 1.76/0.62  fof(f30,plain,(
% 1.76/0.62    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f23])).
% 1.76/0.62  fof(f23,axiom,(
% 1.76/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.76/0.62  fof(f247,plain,(
% 1.76/0.62    spl2_16 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 1.76/0.62    inference(avatar_split_clause,[],[f236,f117,f112,f107,f244])).
% 1.76/0.62  fof(f244,plain,(
% 1.76/0.62    spl2_16 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.76/0.62  fof(f117,plain,(
% 1.76/0.62    spl2_5 <=> v2_pre_topc(sK0)),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.76/0.62  fof(f236,plain,(
% 1.76/0.62    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 1.76/0.62    inference(unit_resulting_resolution,[],[f119,f114,f109,f76])).
% 1.76/0.62  fof(f76,plain,(
% 1.76/0.62    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f40])).
% 1.76/0.62  fof(f40,plain,(
% 1.76/0.62    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.76/0.62    inference(flattening,[],[f39])).
% 1.76/0.62  fof(f39,plain,(
% 1.76/0.62    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.76/0.62    inference(ennf_transformation,[],[f20])).
% 1.76/0.62  fof(f20,axiom,(
% 1.76/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 1.76/0.62  fof(f119,plain,(
% 1.76/0.62    v2_pre_topc(sK0) | ~spl2_5),
% 1.76/0.62    inference(avatar_component_clause,[],[f117])).
% 1.76/0.62  fof(f132,plain,(
% 1.76/0.62    spl2_6 | ~spl2_3),
% 1.76/0.62    inference(avatar_split_clause,[],[f126,f107,f128])).
% 1.76/0.62  fof(f126,plain,(
% 1.76/0.62    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_3),
% 1.76/0.62    inference(resolution,[],[f77,f109])).
% 1.76/0.62  fof(f77,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f53])).
% 1.76/0.62  fof(f120,plain,(
% 1.76/0.62    spl2_5),
% 1.76/0.62    inference(avatar_split_clause,[],[f54,f117])).
% 1.76/0.62  fof(f54,plain,(
% 1.76/0.62    v2_pre_topc(sK0)),
% 1.76/0.62    inference(cnf_transformation,[],[f52])).
% 1.76/0.62  fof(f52,plain,(
% 1.76/0.62    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.76/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).
% 1.76/0.62  fof(f50,plain,(
% 1.76/0.62    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.76/0.62    introduced(choice_axiom,[])).
% 1.76/0.62  fof(f51,plain,(
% 1.76/0.62    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.76/0.62    introduced(choice_axiom,[])).
% 1.76/0.62  fof(f49,plain,(
% 1.76/0.62    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.76/0.62    inference(flattening,[],[f48])).
% 1.76/0.62  fof(f48,plain,(
% 1.76/0.62    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.76/0.62    inference(nnf_transformation,[],[f28])).
% 1.76/0.62  fof(f28,plain,(
% 1.76/0.62    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.76/0.62    inference(flattening,[],[f27])).
% 1.76/0.62  fof(f27,plain,(
% 1.76/0.62    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.76/0.62    inference(ennf_transformation,[],[f26])).
% 1.76/0.62  fof(f26,negated_conjecture,(
% 1.76/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.76/0.62    inference(negated_conjecture,[],[f25])).
% 1.76/0.62  fof(f25,conjecture,(
% 1.76/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 1.76/0.62  fof(f115,plain,(
% 1.76/0.62    spl2_4),
% 1.76/0.62    inference(avatar_split_clause,[],[f55,f112])).
% 1.76/0.62  fof(f55,plain,(
% 1.76/0.62    l1_pre_topc(sK0)),
% 1.76/0.62    inference(cnf_transformation,[],[f52])).
% 1.76/0.62  fof(f110,plain,(
% 1.76/0.62    spl2_3),
% 1.76/0.62    inference(avatar_split_clause,[],[f56,f107])).
% 1.76/0.62  fof(f56,plain,(
% 1.76/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.76/0.62    inference(cnf_transformation,[],[f52])).
% 1.76/0.62  fof(f105,plain,(
% 1.76/0.62    spl2_1 | spl2_2),
% 1.76/0.62    inference(avatar_split_clause,[],[f57,f101,f97])).
% 1.76/0.62  fof(f57,plain,(
% 1.76/0.62    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.76/0.62    inference(cnf_transformation,[],[f52])).
% 1.76/0.62  fof(f104,plain,(
% 1.76/0.62    ~spl2_1 | ~spl2_2),
% 1.76/0.62    inference(avatar_split_clause,[],[f58,f101,f97])).
% 1.76/0.62  fof(f58,plain,(
% 1.76/0.62    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 1.76/0.62    inference(cnf_transformation,[],[f52])).
% 1.76/0.62  % SZS output end Proof for theBenchmark
% 1.76/0.62  % (9090)------------------------------
% 1.76/0.62  % (9090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.62  % (9090)Termination reason: Refutation
% 1.76/0.62  
% 1.76/0.62  % (9090)Memory used [KB]: 8443
% 1.76/0.62  % (9090)Time elapsed: 0.192 s
% 1.76/0.62  % (9090)------------------------------
% 1.76/0.62  % (9090)------------------------------
% 2.15/0.63  % (9083)Success in time 0.269 s
%------------------------------------------------------------------------------
