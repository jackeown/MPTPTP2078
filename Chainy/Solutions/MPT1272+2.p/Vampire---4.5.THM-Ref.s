%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1272+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:15 EST 2020

% Result     : Theorem 19.65s
% Output     : Refutation 19.65s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 144 expanded)
%              Number of leaves         :   17 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  257 ( 405 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10709,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4797,f4821,f4833,f5470,f5478,f5494,f6869,f10538,f10699])).

fof(f10699,plain,
    ( spl280_31
    | ~ spl280_125 ),
    inference(avatar_contradiction_clause,[],[f10698])).

fof(f10698,plain,
    ( $false
    | spl280_31
    | ~ spl280_125 ),
    inference(subsumption_resolution,[],[f10697,f5493])).

fof(f5493,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl280_31 ),
    inference(avatar_component_clause,[],[f5492])).

fof(f5492,plain,
    ( spl280_31
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_31])])).

fof(f10697,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl280_125 ),
    inference(forward_demodulation,[],[f10578,f3969])).

fof(f3969,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f10578,plain,
    ( k1_tops_1(sK0,sK1) = k3_xboole_0(k1_tops_1(sK0,sK1),k1_xboole_0)
    | ~ spl280_125 ),
    inference(resolution,[],[f10537,f3953])).

fof(f3953,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f2696])).

fof(f2696,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f10537,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
    | ~ spl280_125 ),
    inference(avatar_component_clause,[],[f10536])).

fof(f10536,plain,
    ( spl280_125
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_125])])).

fof(f10538,plain,
    ( spl280_125
    | ~ spl280_1
    | ~ spl280_5
    | ~ spl280_27
    | ~ spl280_28
    | ~ spl280_54 ),
    inference(avatar_split_clause,[],[f10531,f6867,f5476,f5468,f4831,f4795,f10536])).

fof(f4795,plain,
    ( spl280_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_1])])).

fof(f4831,plain,
    ( spl280_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_5])])).

fof(f5468,plain,
    ( spl280_27
  <=> v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_27])])).

fof(f5476,plain,
    ( spl280_28
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_28])])).

fof(f6867,plain,
    ( spl280_54
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_54])])).

fof(f10531,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
    | ~ spl280_1
    | ~ spl280_5
    | ~ spl280_27
    | ~ spl280_28
    | ~ spl280_54 ),
    inference(forward_demodulation,[],[f10530,f8003])).

fof(f8003,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl280_1
    | ~ spl280_27
    | ~ spl280_54 ),
    inference(subsumption_resolution,[],[f8002,f5469])).

fof(f5469,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl280_27 ),
    inference(avatar_component_clause,[],[f5468])).

fof(f8002,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl280_1
    | ~ spl280_54 ),
    inference(subsumption_resolution,[],[f7820,f4796])).

fof(f4796,plain,
    ( l1_pre_topc(sK0)
    | ~ spl280_1 ),
    inference(avatar_component_clause,[],[f4795])).

fof(f7820,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl280_54 ),
    inference(resolution,[],[f6868,f3667])).

fof(f3667,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f2522])).

fof(f2522,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2168])).

fof(f2168,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f6868,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl280_54 ),
    inference(avatar_component_clause,[],[f6867])).

fof(f10530,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl280_1
    | ~ spl280_5
    | ~ spl280_28
    | ~ spl280_54 ),
    inference(subsumption_resolution,[],[f10519,f5477])).

fof(f5477,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl280_28 ),
    inference(avatar_component_clause,[],[f5476])).

fof(f10519,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl280_1
    | ~ spl280_5
    | ~ spl280_54 ),
    inference(resolution,[],[f5204,f6868])).

fof(f5204,plain,
    ( ! [X85] :
        ( ~ m1_subset_1(X85,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,X85)
        | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X85)) )
    | ~ spl280_1
    | ~ spl280_5 ),
    inference(subsumption_resolution,[],[f4981,f4796])).

fof(f4981,plain,
    ( ! [X85] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X85,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,X85)
        | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X85)) )
    | ~ spl280_5 ),
    inference(resolution,[],[f4832,f3824])).

fof(f3824,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f2622])).

fof(f2622,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2621])).

fof(f2621,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2139])).

fof(f2139,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f4832,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl280_5 ),
    inference(avatar_component_clause,[],[f4831])).

fof(f6869,plain,
    ( spl280_54
    | ~ spl280_1
    | ~ spl280_5 ),
    inference(avatar_split_clause,[],[f5132,f4831,f4795,f6867])).

fof(f5132,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl280_1
    | ~ spl280_5 ),
    inference(subsumption_resolution,[],[f4915,f4796])).

fof(f4915,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl280_5 ),
    inference(resolution,[],[f4832,f3601])).

fof(f3601,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f2467])).

fof(f2467,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2466])).

fof(f2466,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1780])).

fof(f1780,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f5494,plain,
    ( ~ spl280_31
    | ~ spl280_1
    | ~ spl280_5 ),
    inference(avatar_split_clause,[],[f5177,f4831,f4795,f5492])).

fof(f5177,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ spl280_1
    | ~ spl280_5 ),
    inference(subsumption_resolution,[],[f5176,f5056])).

fof(f5056,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl280_1
    | ~ spl280_5 ),
    inference(subsumption_resolution,[],[f5055,f3173])).

fof(f3173,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f2191])).

fof(f2191,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2190])).

fof(f2190,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2175])).

fof(f2175,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tops_1(X1,X0)
             => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f2174])).

fof(f2174,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

fof(f5055,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl280_1
    | ~ spl280_5 ),
    inference(subsumption_resolution,[],[f4845,f4796])).

fof(f4845,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl280_5 ),
    inference(resolution,[],[f4832,f3188])).

fof(f3188,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f2202])).

fof(f2202,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2092])).

fof(f2092,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f5176,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ spl280_1
    | ~ spl280_5 ),
    inference(subsumption_resolution,[],[f4953,f4796])).

fof(f4953,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ spl280_5 ),
    inference(resolution,[],[f4832,f3666])).

fof(f3666,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f2522])).

fof(f5478,plain,
    ( spl280_28
    | ~ spl280_1
    | ~ spl280_5 ),
    inference(avatar_split_clause,[],[f5149,f4831,f4795,f5476])).

fof(f5149,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl280_1
    | ~ spl280_5 ),
    inference(subsumption_resolution,[],[f4932,f4796])).

fof(f4932,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl280_5 ),
    inference(resolution,[],[f4832,f3619])).

fof(f3619,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f2488])).

fof(f2488,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1839])).

fof(f1839,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f5470,plain,
    ( spl280_27
    | ~ spl280_1
    | ~ spl280_3
    | ~ spl280_5 ),
    inference(avatar_split_clause,[],[f5077,f4831,f4819,f4795,f5468])).

fof(f4819,plain,
    ( spl280_3
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_3])])).

fof(f5077,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl280_1
    | ~ spl280_3
    | ~ spl280_5 ),
    inference(subsumption_resolution,[],[f5076,f4820])).

fof(f4820,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl280_3 ),
    inference(avatar_component_clause,[],[f4819])).

fof(f5076,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ v3_tops_1(sK1,sK0)
    | ~ spl280_1
    | ~ spl280_5 ),
    inference(subsumption_resolution,[],[f4863,f4796])).

fof(f4863,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ v3_tops_1(sK1,sK0)
    | ~ spl280_5 ),
    inference(resolution,[],[f4832,f3242])).

fof(f3242,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f2255])).

fof(f2255,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2093])).

fof(f2093,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

fof(f4833,plain,(
    spl280_5 ),
    inference(avatar_split_clause,[],[f3171,f4831])).

fof(f3171,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2191])).

fof(f4821,plain,(
    spl280_3 ),
    inference(avatar_split_clause,[],[f3172,f4819])).

fof(f3172,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f2191])).

fof(f4797,plain,(
    spl280_1 ),
    inference(avatar_split_clause,[],[f3174,f4795])).

fof(f3174,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2191])).
%------------------------------------------------------------------------------
