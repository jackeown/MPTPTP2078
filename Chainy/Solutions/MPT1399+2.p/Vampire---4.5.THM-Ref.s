%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1399+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:20 EST 2020

% Result     : Theorem 9.57s
% Output     : Refutation 10.09s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 135 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  248 ( 631 expanded)
%              Number of equality atoms :    8 (  40 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4718,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4373,f4628,f4674,f4682,f4703,f4708,f4713,f4717])).

% (14286)Time limit reached!
% (14286)------------------------------
% (14286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14286)Termination reason: Time limit

% (14286)Memory used [KB]: 13176
% (14286)Time elapsed: 1.226 s
% (14286)------------------------------
% (14286)------------------------------
fof(f4717,plain,
    ( ~ spl110_1
    | ~ spl110_8 ),
    inference(avatar_contradiction_clause,[],[f4716])).

fof(f4716,plain,
    ( $false
    | ~ spl110_1
    | ~ spl110_8 ),
    inference(subsumption_resolution,[],[f4715,f3014])).

fof(f3014,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2574])).

fof(f2574,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2573])).

fof(f2573,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2551])).

fof(f2551,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2550])).

fof(f2550,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f4715,plain,
    ( v2_struct_0(sK0)
    | ~ spl110_1
    | ~ spl110_8 ),
    inference(subsumption_resolution,[],[f4714,f4047])).

fof(f4047,plain,
    ( l1_struct_0(sK0)
    | ~ spl110_8 ),
    inference(avatar_component_clause,[],[f4046])).

fof(f4046,plain,
    ( spl110_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl110_8])])).

fof(f4714,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl110_1 ),
    inference(resolution,[],[f3968,f3655])).

fof(f3655,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2976])).

fof(f2976,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2975])).

fof(f2975,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f3968,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl110_1 ),
    inference(avatar_component_clause,[],[f3967])).

fof(f3967,plain,
    ( spl110_1
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl110_1])])).

fof(f4713,plain,
    ( ~ spl110_9
    | spl110_10
    | ~ spl110_8
    | ~ spl110_33
    | ~ spl110_34 ),
    inference(avatar_split_clause,[],[f4712,f4636,f4632,f4046,f4054,f4050])).

fof(f4050,plain,
    ( spl110_9
  <=> r2_hidden(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl110_9])])).

fof(f4054,plain,
    ( spl110_10
  <=> r2_hidden(k2_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl110_10])])).

fof(f4632,plain,
    ( spl110_33
  <=> v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl110_33])])).

fof(f4636,plain,
    ( spl110_34
  <=> v3_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl110_34])])).

fof(f4712,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ spl110_8
    | ~ spl110_33
    | ~ spl110_34 ),
    inference(subsumption_resolution,[],[f4711,f4047])).

fof(f4711,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl110_33
    | ~ spl110_34 ),
    inference(subsumption_resolution,[],[f4684,f4637])).

fof(f4637,plain,
    ( v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl110_34 ),
    inference(avatar_component_clause,[],[f4636])).

fof(f4684,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl110_33 ),
    inference(subsumption_resolution,[],[f4556,f4633])).

fof(f4633,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl110_33 ),
    inference(avatar_component_clause,[],[f4632])).

fof(f4556,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f3959,f3376])).

fof(f3376,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2813])).

fof(f2813,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1781])).

fof(f1781,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f3959,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,k1_xboole_0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3) ) ),
    inference(forward_demodulation,[],[f3010,f3012])).

fof(f3012,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f2574])).

fof(f3010,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f2574])).

fof(f4708,plain,
    ( spl110_1
    | spl110_3 ),
    inference(avatar_split_clause,[],[f4369,f3976,f3967])).

fof(f3976,plain,
    ( spl110_3
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl110_3])])).

fof(f4369,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f3013,f3353])).

fof(f3353,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2795])).

fof(f2795,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f3013,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2574])).

fof(f4703,plain,(
    ~ spl110_10 ),
    inference(avatar_contradiction_clause,[],[f4702])).

fof(f4702,plain,
    ( $false
    | ~ spl110_10 ),
    inference(subsumption_resolution,[],[f4696,f3372])).

fof(f3372,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f4696,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl110_10 ),
    inference(resolution,[],[f4055,f3357])).

fof(f3357,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f4055,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl110_10 ),
    inference(avatar_component_clause,[],[f4054])).

fof(f4682,plain,(
    spl110_34 ),
    inference(avatar_contradiction_clause,[],[f4681])).

fof(f4681,plain,
    ( $false
    | spl110_34 ),
    inference(subsumption_resolution,[],[f4680,f3015])).

fof(f3015,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2574])).

fof(f4680,plain,
    ( ~ v2_pre_topc(sK0)
    | spl110_34 ),
    inference(subsumption_resolution,[],[f4678,f3016])).

fof(f3016,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2574])).

fof(f4678,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl110_34 ),
    inference(resolution,[],[f4638,f3374])).

fof(f3374,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2810])).

fof(f2810,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2809])).

fof(f2809,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2104])).

fof(f2104,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f4638,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | spl110_34 ),
    inference(avatar_component_clause,[],[f4636])).

fof(f4674,plain,(
    spl110_33 ),
    inference(avatar_contradiction_clause,[],[f4673])).

fof(f4673,plain,
    ( $false
    | spl110_33 ),
    inference(subsumption_resolution,[],[f4672,f3015])).

fof(f4672,plain,
    ( ~ v2_pre_topc(sK0)
    | spl110_33 ),
    inference(subsumption_resolution,[],[f4670,f3016])).

fof(f4670,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl110_33 ),
    inference(resolution,[],[f4634,f3055])).

fof(f3055,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2609])).

fof(f2609,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2608])).

fof(f2608,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1798])).

fof(f1798,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f4634,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | spl110_33 ),
    inference(avatar_component_clause,[],[f4632])).

fof(f4628,plain,
    ( ~ spl110_3
    | ~ spl110_8
    | spl110_9 ),
    inference(avatar_contradiction_clause,[],[f4627])).

fof(f4627,plain,
    ( $false
    | ~ spl110_3
    | ~ spl110_8
    | spl110_9 ),
    inference(subsumption_resolution,[],[f4626,f4047])).

fof(f4626,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl110_3
    | spl110_9 ),
    inference(subsumption_resolution,[],[f4625,f3978])).

fof(f3978,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl110_3 ),
    inference(avatar_component_clause,[],[f3976])).

fof(f4625,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | spl110_9 ),
    inference(superposition,[],[f4051,f3377])).

fof(f3377,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2814])).

fof(f2814,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f4051,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | spl110_9 ),
    inference(avatar_component_clause,[],[f4050])).

fof(f4373,plain,(
    spl110_8 ),
    inference(avatar_contradiction_clause,[],[f4372])).

fof(f4372,plain,
    ( $false
    | spl110_8 ),
    inference(subsumption_resolution,[],[f4371,f3016])).

fof(f4371,plain,
    ( ~ l1_pre_topc(sK0)
    | spl110_8 ),
    inference(resolution,[],[f4048,f3656])).

fof(f3656,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2977])).

fof(f2977,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f4048,plain,
    ( ~ l1_struct_0(sK0)
    | spl110_8 ),
    inference(avatar_component_clause,[],[f4046])).
%------------------------------------------------------------------------------
