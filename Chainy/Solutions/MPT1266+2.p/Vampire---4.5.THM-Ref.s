%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1266+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:15 EST 2020

% Result     : Theorem 21.62s
% Output     : Refutation 21.62s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 324 expanded)
%              Number of leaves         :   38 ( 123 expanded)
%              Depth                    :   13
%              Number of atoms          :  491 ( 927 expanded)
%              Number of equality atoms :  111 ( 220 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34621,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3401,f3411,f3430,f3493,f3750,f4000,f4503,f4932,f4966,f5106,f8945,f10251,f12663,f14815,f15061,f17336,f17513,f17701,f34618,f34620])).

fof(f34620,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),sK1)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f34618,plain,
    ( ~ spl90_1
    | spl90_57
    | ~ spl90_58
    | ~ spl90_59
    | ~ spl90_119
    | ~ spl90_126
    | ~ spl90_145 ),
    inference(avatar_contradiction_clause,[],[f34617])).

fof(f34617,plain,
    ( $false
    | ~ spl90_1
    | spl90_57
    | ~ spl90_58
    | ~ spl90_59
    | ~ spl90_119
    | ~ spl90_126
    | ~ spl90_145 ),
    inference(subsumption_resolution,[],[f34616,f14415])).

fof(f14415,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl90_1
    | ~ spl90_145 ),
    inference(unit_resulting_resolution,[],[f3400,f12662,f2893])).

fof(f2893,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f2296])).

fof(f2296,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2295])).

fof(f2295,plain,(
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

fof(f12662,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl90_145 ),
    inference(avatar_component_clause,[],[f12660])).

fof(f12660,plain,
    ( spl90_145
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl90_145])])).

fof(f3400,plain,
    ( l1_pre_topc(sK0)
    | ~ spl90_1 ),
    inference(avatar_component_clause,[],[f3398])).

fof(f3398,plain,
    ( spl90_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl90_1])])).

fof(f34616,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl90_1
    | spl90_57
    | ~ spl90_58
    | ~ spl90_59
    | ~ spl90_119
    | ~ spl90_126
    | ~ spl90_145 ),
    inference(subsumption_resolution,[],[f34614,f17335])).

fof(f17335,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl90_1
    | spl90_57
    | ~ spl90_126
    | ~ spl90_145 ),
    inference(forward_demodulation,[],[f17334,f10346])).

fof(f10346,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl90_126 ),
    inference(unit_resulting_resolution,[],[f10250,f2877])).

fof(f2877,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2273])).

fof(f2273,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f10250,plain,
    ( l1_struct_0(sK0)
    | ~ spl90_126 ),
    inference(avatar_component_clause,[],[f10248])).

fof(f10248,plain,
    ( spl90_126
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl90_126])])).

fof(f17334,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl90_1
    | spl90_57
    | ~ spl90_145 ),
    inference(unit_resulting_resolution,[],[f3400,f12662,f4930,f2963])).

fof(f2963,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f2661])).

fof(f2661,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2350])).

fof(f2350,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2090])).

fof(f2090,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f4930,plain,
    ( ~ v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | spl90_57 ),
    inference(avatar_component_clause,[],[f4929])).

fof(f4929,plain,
    ( spl90_57
  <=> v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl90_57])])).

fof(f34614,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl90_58
    | ~ spl90_59
    | ~ spl90_119
    | ~ spl90_126 ),
    inference(trivial_inequality_removal,[],[f34609])).

fof(f34609,plain,
    ( k1_xboole_0 != k1_xboole_0
    | u1_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl90_58
    | ~ spl90_59
    | ~ spl90_119
    | ~ spl90_126 ),
    inference(superposition,[],[f10392,f4972])).

fof(f4972,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl90_59 ),
    inference(avatar_component_clause,[],[f4971])).

fof(f4971,plain,
    ( spl90_59
  <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl90_59])])).

fof(f10392,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),X0)
        | u1_struct_0(sK0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl90_58
    | ~ spl90_119
    | ~ spl90_126 ),
    inference(forward_demodulation,[],[f10391,f10361])).

fof(f10361,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ spl90_119
    | ~ spl90_126 ),
    inference(backward_demodulation,[],[f8944,f10346])).

fof(f8944,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl90_119 ),
    inference(avatar_component_clause,[],[f8942])).

fof(f8942,plain,
    ( spl90_119
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl90_119])])).

fof(f10391,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),X0)
        | k2_pre_topc(sK0,u1_struct_0(sK0)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl90_58
    | ~ spl90_119
    | ~ spl90_126 ),
    inference(subsumption_resolution,[],[f10375,f4455])).

fof(f4455,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f3293,f2822])).

fof(f2822,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2586])).

fof(f2586,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f3293,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2831])).

fof(f2831,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2596])).

fof(f2596,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2595])).

fof(f2595,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f10375,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),X0)
        | k2_pre_topc(sK0,u1_struct_0(sK0)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl90_58
    | ~ spl90_119
    | ~ spl90_126 ),
    inference(backward_demodulation,[],[f7086,f10361])).

fof(f7086,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),X0)
        | k2_pre_topc(sK0,u1_struct_0(sK0)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl90_58 ),
    inference(superposition,[],[f2936,f4965])).

fof(f4965,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl90_58 ),
    inference(avatar_component_clause,[],[f4963])).

fof(f4963,plain,
    ( spl90_58
  <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl90_58])])).

fof(f2936,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X1) != k3_subset_1(X0,X2)
      | X1 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2322])).

fof(f2322,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | k3_subset_1(X0,X1) != k3_subset_1(X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f2321])).

fof(f2321,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | k3_subset_1(X0,X1) != k3_subset_1(X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f536])).

fof(f536,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_subset_1)).

fof(f17701,plain,
    ( spl90_168
    | ~ spl90_3 ),
    inference(avatar_split_clause,[],[f4890,f3408,f17698])).

fof(f17698,plain,
    ( spl90_168
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl90_168])])).

fof(f3408,plain,
    ( spl90_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl90_3])])).

fof(f4890,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl90_3 ),
    inference(unit_resulting_resolution,[],[f3410,f2940])).

fof(f2940,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2328])).

fof(f2328,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f3410,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl90_3 ),
    inference(avatar_component_clause,[],[f3408])).

fof(f17513,plain,
    ( ~ spl90_6
    | ~ spl90_1
    | ~ spl90_3
    | spl90_26 ),
    inference(avatar_split_clause,[],[f3792,f3738,f3408,f3398,f3423])).

fof(f3423,plain,
    ( spl90_6
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl90_6])])).

fof(f3738,plain,
    ( spl90_26
  <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl90_26])])).

fof(f3792,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl90_1
    | ~ spl90_3
    | spl90_26 ),
    inference(unit_resulting_resolution,[],[f3400,f3410,f3739,f2797])).

fof(f2797,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2571])).

fof(f2571,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2209])).

fof(f2209,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2091])).

fof(f2091,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f3739,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl90_26 ),
    inference(avatar_component_clause,[],[f3738])).

fof(f17336,plain,
    ( spl90_7
    | ~ spl90_59
    | ~ spl90_60 ),
    inference(avatar_split_clause,[],[f15151,f5103,f4971,f3427])).

fof(f3427,plain,
    ( spl90_7
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl90_7])])).

fof(f5103,plain,
    ( spl90_60
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl90_60])])).

fof(f15151,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl90_59
    | ~ spl90_60 ),
    inference(backward_demodulation,[],[f5105,f4972])).

fof(f5105,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl90_60 ),
    inference(avatar_component_clause,[],[f5103])).

fof(f15061,plain,
    ( k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1)
    | k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f14815,plain,
    ( ~ spl90_1
    | ~ spl90_57
    | spl90_59
    | ~ spl90_126
    | ~ spl90_145 ),
    inference(avatar_contradiction_clause,[],[f14814])).

fof(f14814,plain,
    ( $false
    | ~ spl90_1
    | ~ spl90_57
    | spl90_59
    | ~ spl90_126
    | ~ spl90_145 ),
    inference(subsumption_resolution,[],[f14796,f4918])).

fof(f4918,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f4882,f4912])).

fof(f4912,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f4888,f3283])).

fof(f3283,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f4888,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f2795,f2940])).

fof(f2795,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f4882,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f2795,f2939])).

fof(f2939,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f2327])).

fof(f2327,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f487])).

fof(f487,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f14796,plain,
    ( k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl90_1
    | ~ spl90_57
    | spl90_59
    | ~ spl90_126
    | ~ spl90_145 ),
    inference(backward_demodulation,[],[f4973,f14793])).

fof(f14793,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl90_1
    | ~ spl90_57
    | ~ spl90_126
    | ~ spl90_145 ),
    inference(forward_demodulation,[],[f14422,f10346])).

fof(f14422,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl90_1
    | ~ spl90_57
    | ~ spl90_145 ),
    inference(unit_resulting_resolution,[],[f3400,f4931,f12662,f2962])).

fof(f2962,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2661])).

fof(f4931,plain,
    ( v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl90_57 ),
    inference(avatar_component_clause,[],[f4929])).

fof(f4973,plain,
    ( k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))
    | spl90_59 ),
    inference(avatar_component_clause,[],[f4971])).

fof(f12663,plain,
    ( spl90_145
    | ~ spl90_3 ),
    inference(avatar_split_clause,[],[f4905,f3408,f12660])).

fof(f4905,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl90_3 ),
    inference(backward_demodulation,[],[f4746,f4890])).

fof(f4746,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl90_3 ),
    inference(unit_resulting_resolution,[],[f3410,f2941])).

fof(f2941,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2329])).

fof(f2329,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f466])).

fof(f466,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f10251,plain,
    ( spl90_126
    | ~ spl90_1 ),
    inference(avatar_split_clause,[],[f10245,f3398,f10248])).

fof(f10245,plain,
    ( l1_struct_0(sK0)
    | ~ spl90_1 ),
    inference(unit_resulting_resolution,[],[f3400,f3096])).

fof(f3096,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2430])).

fof(f2430,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f8945,plain,
    ( spl90_119
    | ~ spl90_1 ),
    inference(avatar_split_clause,[],[f4689,f3398,f8942])).

fof(f4689,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl90_1 ),
    inference(unit_resulting_resolution,[],[f3400,f2878])).

fof(f2878,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f2274])).

fof(f2274,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2118])).

fof(f2118,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

fof(f5106,plain,
    ( spl90_60
    | ~ spl90_3
    | ~ spl90_44 ),
    inference(avatar_split_clause,[],[f4902,f4500,f3408,f5103])).

fof(f4500,plain,
    ( spl90_44
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl90_44])])).

fof(f4902,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl90_3
    | ~ spl90_44 ),
    inference(backward_demodulation,[],[f4502,f4890])).

fof(f4502,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl90_44 ),
    inference(avatar_component_clause,[],[f4500])).

fof(f4966,plain,
    ( spl90_58
    | ~ spl90_35 ),
    inference(avatar_split_clause,[],[f4915,f3997,f4963])).

fof(f3997,plain,
    ( spl90_35
  <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl90_35])])).

fof(f4915,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl90_35 ),
    inference(backward_demodulation,[],[f3999,f4912])).

fof(f3999,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl90_35 ),
    inference(avatar_component_clause,[],[f3997])).

fof(f4932,plain,
    ( spl90_57
    | ~ spl90_3
    | ~ spl90_26 ),
    inference(avatar_split_clause,[],[f4900,f3738,f3408,f4929])).

fof(f4900,plain,
    ( v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl90_3
    | ~ spl90_26 ),
    inference(backward_demodulation,[],[f3740,f4890])).

fof(f3740,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl90_26 ),
    inference(avatar_component_clause,[],[f3738])).

fof(f4503,plain,
    ( spl90_44
    | ~ spl90_1
    | ~ spl90_3 ),
    inference(avatar_split_clause,[],[f3555,f3408,f3398,f4500])).

fof(f3555,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl90_1
    | ~ spl90_3 ),
    inference(unit_resulting_resolution,[],[f3400,f3410,f2775])).

fof(f2775,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f2194])).

fof(f2194,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2088])).

fof(f2088,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f4000,plain,
    ( spl90_35
    | ~ spl90_1
    | ~ spl90_16 ),
    inference(avatar_split_clause,[],[f3653,f3490,f3398,f3997])).

fof(f3490,plain,
    ( spl90_16
  <=> r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl90_16])])).

fof(f3653,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl90_1
    | ~ spl90_16 ),
    inference(backward_demodulation,[],[f3556,f3647])).

fof(f3647,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl90_16 ),
    inference(unit_resulting_resolution,[],[f3492,f2794])).

fof(f2794,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2208])).

fof(f2208,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f3492,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl90_16 ),
    inference(avatar_component_clause,[],[f3490])).

fof(f3556,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl90_1 ),
    inference(unit_resulting_resolution,[],[f3400,f2795,f2775])).

fof(f3750,plain,
    ( ~ spl90_1
    | ~ spl90_3
    | ~ spl90_7
    | ~ spl90_26 ),
    inference(avatar_contradiction_clause,[],[f3749])).

fof(f3749,plain,
    ( $false
    | ~ spl90_1
    | ~ spl90_3
    | ~ spl90_7
    | ~ spl90_26 ),
    inference(subsumption_resolution,[],[f3432,f3742])).

fof(f3742,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl90_1
    | ~ spl90_3
    | ~ spl90_26 ),
    inference(unit_resulting_resolution,[],[f3400,f3410,f3740,f2798])).

fof(f2798,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2571])).

fof(f3432,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl90_7 ),
    inference(trivial_inequality_removal,[],[f3431])).

fof(f3431,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl90_7 ),
    inference(backward_demodulation,[],[f2757,f3429])).

fof(f3429,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl90_7 ),
    inference(avatar_component_clause,[],[f3427])).

fof(f2757,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f2560])).

fof(f2560,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2557,f2559,f2558])).

fof(f2558,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_xboole_0 != k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
            | ~ v2_tops_1(X1,sK0) )
          & ( k1_xboole_0 = k1_tops_1(sK0,X1)
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2559,plain,
    ( ? [X1] :
        ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
          | ~ v2_tops_1(X1,sK0) )
        & ( k1_xboole_0 = k1_tops_1(sK0,X1)
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
        | ~ v2_tops_1(sK1,sK0) )
      & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2557,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2556])).

fof(f2556,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2171])).

fof(f2171,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2165])).

fof(f2165,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f2164])).

fof(f2164,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f3493,plain,
    ( spl90_16
    | ~ spl90_1 ),
    inference(avatar_split_clause,[],[f3484,f3398,f3490])).

fof(f3484,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl90_1 ),
    inference(unit_resulting_resolution,[],[f3400,f2795,f2776])).

fof(f2776,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f2195])).

fof(f2195,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2132])).

fof(f2132,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f3430,plain,
    ( spl90_6
    | spl90_7 ),
    inference(avatar_split_clause,[],[f2756,f3427,f3423])).

fof(f2756,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f2560])).

fof(f3411,plain,(
    spl90_3 ),
    inference(avatar_split_clause,[],[f2755,f3408])).

fof(f2755,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2560])).

fof(f3401,plain,(
    spl90_1 ),
    inference(avatar_split_clause,[],[f2754,f3398])).

fof(f2754,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2560])).
%------------------------------------------------------------------------------
