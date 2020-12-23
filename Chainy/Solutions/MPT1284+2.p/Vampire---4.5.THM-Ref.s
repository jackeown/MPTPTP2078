%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1284+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:16 EST 2020

% Result     : Theorem 11.17s
% Output     : Refutation 11.17s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 358 expanded)
%              Number of leaves         :   34 ( 162 expanded)
%              Depth                    :   13
%              Number of atoms          :  608 (2147 expanded)
%              Number of equality atoms :   30 (  54 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17684,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3467,f3472,f3477,f3487,f3497,f3511,f3521,f3531,f3545,f3546,f3547,f3726,f3823,f6815,f9077,f9094,f10221,f10444,f10665,f17280,f17316,f17683])).

fof(f17683,plain,
    ( ~ spl93_2
    | ~ spl93_5
    | ~ spl93_16
    | spl93_17
    | ~ spl93_31
    | ~ spl93_33
    | ~ spl93_100
    | ~ spl93_102 ),
    inference(avatar_contradiction_clause,[],[f17682])).

fof(f17682,plain,
    ( $false
    | ~ spl93_2
    | ~ spl93_5
    | ~ spl93_16
    | spl93_17
    | ~ spl93_31
    | ~ spl93_33
    | ~ spl93_100
    | ~ spl93_102 ),
    inference(subsumption_resolution,[],[f4061,f17457])).

fof(f17457,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl93_2
    | ~ spl93_5
    | ~ spl93_16
    | ~ spl93_100
    | ~ spl93_102 ),
    inference(forward_demodulation,[],[f10451,f3935])).

fof(f3935,plain,
    ( sK2 = k2_pre_topc(sK0,sK2)
    | ~ spl93_2
    | ~ spl93_5
    | ~ spl93_16 ),
    inference(unit_resulting_resolution,[],[f3471,f3486,f3539,f2837])).

fof(f2837,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f2242])).

fof(f2242,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2241])).

fof(f2241,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1843])).

fof(f1843,axiom,(
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

fof(f3539,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl93_16 ),
    inference(avatar_component_clause,[],[f3538])).

fof(f3538,plain,
    ( spl93_16
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_16])])).

fof(f3486,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl93_5 ),
    inference(avatar_component_clause,[],[f3484])).

fof(f3484,plain,
    ( spl93_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_5])])).

fof(f3471,plain,
    ( l1_pre_topc(sK0)
    | ~ spl93_2 ),
    inference(avatar_component_clause,[],[f3469])).

fof(f3469,plain,
    ( spl93_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_2])])).

fof(f10451,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k2_pre_topc(sK0,sK2))
    | ~ spl93_100
    | ~ spl93_102 ),
    inference(unit_resulting_resolution,[],[f10220,f10443,f2887])).

fof(f2887,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f2282])).

fof(f2282,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2281])).

fof(f2281,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f10443,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl93_102 ),
    inference(avatar_component_clause,[],[f10441])).

fof(f10441,plain,
    ( spl93_102
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_102])])).

fof(f10220,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl93_100 ),
    inference(avatar_component_clause,[],[f10218])).

fof(f10218,plain,
    ( spl93_100
  <=> r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_100])])).

fof(f4061,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl93_2
    | ~ spl93_5
    | spl93_17
    | ~ spl93_31
    | ~ spl93_33 ),
    inference(subsumption_resolution,[],[f4060,f3355])).

fof(f3355,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2899])).

fof(f2899,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2640])).

fof(f2640,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2639])).

fof(f2639,plain,(
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

fof(f4060,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl93_2
    | ~ spl93_5
    | spl93_17
    | ~ spl93_31
    | ~ spl93_33 ),
    inference(forward_demodulation,[],[f4059,f3702])).

fof(f3702,plain,
    ( sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | ~ spl93_33 ),
    inference(avatar_component_clause,[],[f3700])).

fof(f3700,plain,
    ( spl93_33
  <=> sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_33])])).

fof(f4059,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ spl93_2
    | ~ spl93_5
    | spl93_17
    | ~ spl93_31 ),
    inference(subsumption_resolution,[],[f4058,f3471])).

fof(f4058,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ spl93_5
    | spl93_17
    | ~ spl93_31 ),
    inference(subsumption_resolution,[],[f4057,f3486])).

fof(f4057,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl93_17
    | ~ spl93_31 ),
    inference(subsumption_resolution,[],[f4051,f3544])).

fof(f3544,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | spl93_17 ),
    inference(avatar_component_clause,[],[f3542])).

fof(f3542,plain,
    ( spl93_17
  <=> v4_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_17])])).

fof(f4051,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl93_31 ),
    inference(superposition,[],[f2802,f3690])).

fof(f3690,plain,
    ( sK2 = k2_pre_topc(sK0,sK2)
    | ~ spl93_31 ),
    inference(avatar_component_clause,[],[f3689])).

fof(f3689,plain,
    ( spl93_31
  <=> sK2 = k2_pre_topc(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_31])])).

fof(f2802,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2586])).

fof(f2586,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2585])).

fof(f2585,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2212])).

fof(f2212,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2097])).

fof(f2097,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

fof(f17316,plain,
    ( ~ spl93_3
    | ~ spl93_7
    | ~ spl93_9
    | ~ spl93_103
    | spl93_142 ),
    inference(avatar_contradiction_clause,[],[f17315])).

fof(f17315,plain,
    ( $false
    | ~ spl93_3
    | ~ spl93_7
    | ~ spl93_9
    | ~ spl93_103
    | spl93_142 ),
    inference(subsumption_resolution,[],[f17281,f6808])).

fof(f6808,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl93_3
    | ~ spl93_7 ),
    inference(unit_resulting_resolution,[],[f3476,f3496,f2868])).

fof(f2868,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2259])).

fof(f2259,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2258])).

fof(f2258,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2100])).

fof(f2100,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f3496,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl93_7 ),
    inference(avatar_component_clause,[],[f3494])).

fof(f3494,plain,
    ( spl93_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_7])])).

fof(f3476,plain,
    ( l1_pre_topc(sK1)
    | ~ spl93_3 ),
    inference(avatar_component_clause,[],[f3474])).

fof(f3474,plain,
    ( spl93_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_3])])).

fof(f17281,plain,
    ( ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl93_3
    | ~ spl93_7
    | ~ spl93_9
    | ~ spl93_103
    | spl93_142 ),
    inference(unit_resulting_resolution,[],[f3476,f3506,f3496,f10664,f17279,f2827])).

fof(f2827,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2236])).

fof(f2236,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2235])).

fof(f2235,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2144])).

fof(f2144,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

fof(f17279,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)
    | spl93_142 ),
    inference(avatar_component_clause,[],[f17277])).

fof(f17277,plain,
    ( spl93_142
  <=> r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_142])])).

fof(f10664,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),sK3)
    | ~ spl93_103 ),
    inference(avatar_component_clause,[],[f10662])).

fof(f10662,plain,
    ( spl93_103
  <=> r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_103])])).

fof(f3506,plain,
    ( v4_pre_topc(sK3,sK1)
    | ~ spl93_9 ),
    inference(avatar_component_clause,[],[f3504])).

fof(f3504,plain,
    ( spl93_9
  <=> v4_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_9])])).

fof(f17280,plain,
    ( ~ spl93_142
    | spl93_34
    | ~ spl93_40 ),
    inference(avatar_split_clause,[],[f4495,f3820,f3723,f17277])).

fof(f3723,plain,
    ( spl93_34
  <=> sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_34])])).

fof(f3820,plain,
    ( spl93_40
  <=> r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_40])])).

fof(f4495,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)
    | spl93_34
    | ~ spl93_40 ),
    inference(unit_resulting_resolution,[],[f3725,f3822,f2900])).

fof(f2900,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2640])).

fof(f3822,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ spl93_40 ),
    inference(avatar_component_clause,[],[f3820])).

fof(f3725,plain,
    ( sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | spl93_34 ),
    inference(avatar_component_clause,[],[f3723])).

fof(f10665,plain,
    ( spl93_103
    | ~ spl93_3
    | ~ spl93_7 ),
    inference(avatar_split_clause,[],[f5577,f3494,f3474,f10662])).

fof(f5577,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),sK3)
    | ~ spl93_3
    | ~ spl93_7 ),
    inference(unit_resulting_resolution,[],[f3476,f3496,f2886])).

fof(f2886,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f2280])).

fof(f2280,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2155])).

fof(f2155,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f10444,plain,
    ( spl93_102
    | ~ spl93_2
    | ~ spl93_5 ),
    inference(avatar_split_clause,[],[f5576,f3484,f3469,f10441])).

fof(f5576,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl93_2
    | ~ spl93_5 ),
    inference(unit_resulting_resolution,[],[f3471,f3486,f2886])).

fof(f10221,plain,
    ( spl93_100
    | ~ spl93_2
    | ~ spl93_5 ),
    inference(avatar_split_clause,[],[f5520,f3484,f3469,f10218])).

fof(f5520,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl93_2
    | ~ spl93_5 ),
    inference(unit_resulting_resolution,[],[f3471,f3486,f2866])).

fof(f2866,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f2255])).

fof(f2255,plain,(
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

fof(f9094,plain,
    ( ~ spl93_10
    | ~ spl93_2
    | ~ spl93_5
    | spl93_33 ),
    inference(avatar_split_clause,[],[f3799,f3700,f3484,f3469,f3508])).

fof(f3508,plain,
    ( spl93_10
  <=> v5_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_10])])).

fof(f3799,plain,
    ( ~ v5_tops_1(sK2,sK0)
    | ~ spl93_2
    | ~ spl93_5
    | spl93_33 ),
    inference(unit_resulting_resolution,[],[f3471,f3486,f3701,f2796])).

fof(f2796,plain,(
    ! [X0,X1] :
      ( ~ v5_tops_1(X1,X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2584])).

fof(f2584,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2207])).

fof(f2207,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2098])).

fof(f2098,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

fof(f3701,plain,
    ( sK2 != k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | spl93_33 ),
    inference(avatar_component_clause,[],[f3700])).

fof(f9077,plain,
    ( ~ spl93_16
    | ~ spl93_2
    | ~ spl93_5
    | spl93_31 ),
    inference(avatar_split_clause,[],[f3693,f3689,f3484,f3469,f3538])).

fof(f3693,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | ~ spl93_2
    | ~ spl93_5
    | spl93_31 ),
    inference(unit_resulting_resolution,[],[f3471,f3486,f3691,f2837])).

fof(f3691,plain,
    ( sK2 != k2_pre_topc(sK0,sK2)
    | spl93_31 ),
    inference(avatar_component_clause,[],[f3689])).

fof(f6815,plain,
    ( ~ spl93_1
    | ~ spl93_2
    | ~ spl93_5
    | spl93_16
    | ~ spl93_33 ),
    inference(avatar_contradiction_clause,[],[f6814])).

fof(f6814,plain,
    ( $false
    | ~ spl93_1
    | ~ spl93_2
    | ~ spl93_5
    | spl93_16
    | ~ spl93_33 ),
    inference(subsumption_resolution,[],[f6807,f3721])).

fof(f3721,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl93_1
    | ~ spl93_2
    | spl93_16
    | ~ spl93_33 ),
    inference(subsumption_resolution,[],[f3720,f3466])).

fof(f3466,plain,
    ( v2_pre_topc(sK0)
    | ~ spl93_1 ),
    inference(avatar_component_clause,[],[f3464])).

fof(f3464,plain,
    ( spl93_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_1])])).

fof(f3720,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl93_2
    | spl93_16
    | ~ spl93_33 ),
    inference(subsumption_resolution,[],[f3719,f3471])).

fof(f3719,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl93_16
    | ~ spl93_33 ),
    inference(subsumption_resolution,[],[f3712,f3540])).

fof(f3540,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | spl93_16 ),
    inference(avatar_component_clause,[],[f3538])).

fof(f3712,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl93_33 ),
    inference(superposition,[],[f2811,f3702])).

fof(f2811,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2220])).

fof(f2220,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2219])).

fof(f2219,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2111])).

fof(f2111,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f6807,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl93_2
    | ~ spl93_5 ),
    inference(unit_resulting_resolution,[],[f3471,f3486,f2868])).

fof(f3823,plain,
    ( spl93_40
    | ~ spl93_3
    | ~ spl93_7
    | ~ spl93_12 ),
    inference(avatar_split_clause,[],[f3795,f3518,f3494,f3474,f3820])).

fof(f3518,plain,
    ( spl93_12
  <=> v4_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_12])])).

fof(f3795,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ spl93_3
    | ~ spl93_7
    | ~ spl93_12 ),
    inference(unit_resulting_resolution,[],[f3476,f3496,f3520,f2801])).

fof(f2801,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2586])).

fof(f3520,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ spl93_12 ),
    inference(avatar_component_clause,[],[f3518])).

fof(f3726,plain,
    ( ~ spl93_34
    | ~ spl93_3
    | ~ spl93_7
    | spl93_14 ),
    inference(avatar_split_clause,[],[f3579,f3528,f3494,f3474,f3723])).

fof(f3528,plain,
    ( spl93_14
  <=> v5_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl93_14])])).

fof(f3579,plain,
    ( sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | ~ spl93_3
    | ~ spl93_7
    | spl93_14 ),
    inference(unit_resulting_resolution,[],[f3476,f3530,f3496,f2797])).

fof(f2797,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2584])).

fof(f3530,plain,
    ( ~ v5_tops_1(sK3,sK1)
    | spl93_14 ),
    inference(avatar_component_clause,[],[f3528])).

fof(f3547,plain,
    ( ~ spl93_14
    | ~ spl93_16
    | ~ spl93_17 ),
    inference(avatar_split_clause,[],[f2795,f3542,f3538,f3528])).

fof(f2795,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v5_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f2583])).

fof(f2583,plain,
    ( ( ( ( ~ v4_tops_1(sK2,sK0)
          | ~ v4_pre_topc(sK2,sK0) )
        & v5_tops_1(sK2,sK0) )
      | ( ~ v5_tops_1(sK3,sK1)
        & v4_tops_1(sK3,sK1)
        & v4_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2206,f2582,f2581,f2580,f2579])).

fof(f2579,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v4_pre_topc(X2,X0) )
                        & v5_tops_1(X2,X0) )
                      | ( ~ v5_tops_1(X3,X1)
                        & v4_tops_1(X3,X1)
                        & v4_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK0)
                        | ~ v4_pre_topc(X2,sK0) )
                      & v5_tops_1(X2,sK0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2580,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,sK0)
                      | ~ v4_pre_topc(X2,sK0) )
                    & v5_tops_1(X2,sK0) )
                  | ( ~ v5_tops_1(X3,X1)
                    & v4_tops_1(X3,X1)
                    & v4_pre_topc(X3,X1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,sK0)
                    | ~ v4_pre_topc(X2,sK0) )
                  & v5_tops_1(X2,sK0) )
                | ( ~ v5_tops_1(X3,sK1)
                  & v4_tops_1(X3,sK1)
                  & v4_pre_topc(X3,sK1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f2581,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(X2,sK0)
                  | ~ v4_pre_topc(X2,sK0) )
                & v5_tops_1(X2,sK0) )
              | ( ~ v5_tops_1(X3,sK1)
                & v4_tops_1(X3,sK1)
                & v4_pre_topc(X3,sK1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(sK2,sK0)
                | ~ v4_pre_topc(sK2,sK0) )
              & v5_tops_1(sK2,sK0) )
            | ( ~ v5_tops_1(X3,sK1)
              & v4_tops_1(X3,sK1)
              & v4_pre_topc(X3,sK1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2582,plain,
    ( ? [X3] :
        ( ( ( ( ~ v4_tops_1(sK2,sK0)
              | ~ v4_pre_topc(sK2,sK0) )
            & v5_tops_1(sK2,sK0) )
          | ( ~ v5_tops_1(X3,sK1)
            & v4_tops_1(X3,sK1)
            & v4_pre_topc(X3,sK1) ) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ( ( ~ v4_tops_1(sK2,sK0)
            | ~ v4_pre_topc(sK2,sK0) )
          & v5_tops_1(sK2,sK0) )
        | ( ~ v5_tops_1(sK3,sK1)
          & v4_tops_1(sK3,sK1)
          & v4_pre_topc(sK3,sK1) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f2206,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2205])).

fof(f2205,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2139])).

fof(f2139,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v5_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v4_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v4_pre_topc(X3,X1) )
                       => v5_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2138])).

fof(f2138,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v5_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v4_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v4_pre_topc(X3,X1) )
                     => v5_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tops_1)).

fof(f3546,plain,
    ( spl93_12
    | ~ spl93_16
    | ~ spl93_17 ),
    inference(avatar_split_clause,[],[f2794,f3542,f3538,f3518])).

fof(f2794,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f2583])).

fof(f3545,plain,
    ( spl93_9
    | ~ spl93_16
    | ~ spl93_17 ),
    inference(avatar_split_clause,[],[f2793,f3542,f3538,f3504])).

fof(f2793,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f2583])).

fof(f3531,plain,
    ( ~ spl93_14
    | spl93_10 ),
    inference(avatar_split_clause,[],[f2792,f3508,f3528])).

fof(f2792,plain,
    ( v5_tops_1(sK2,sK0)
    | ~ v5_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f2583])).

fof(f3521,plain,
    ( spl93_12
    | spl93_10 ),
    inference(avatar_split_clause,[],[f2791,f3508,f3518])).

fof(f2791,plain,
    ( v5_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f2583])).

fof(f3511,plain,
    ( spl93_9
    | spl93_10 ),
    inference(avatar_split_clause,[],[f2790,f3508,f3504])).

fof(f2790,plain,
    ( v5_tops_1(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f2583])).

fof(f3497,plain,(
    spl93_7 ),
    inference(avatar_split_clause,[],[f2789,f3494])).

fof(f2789,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f2583])).

fof(f3487,plain,(
    spl93_5 ),
    inference(avatar_split_clause,[],[f2788,f3484])).

fof(f2788,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2583])).

fof(f3477,plain,(
    spl93_3 ),
    inference(avatar_split_clause,[],[f2787,f3474])).

fof(f2787,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f2583])).

fof(f3472,plain,(
    spl93_2 ),
    inference(avatar_split_clause,[],[f2786,f3469])).

fof(f2786,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2583])).

fof(f3467,plain,(
    spl93_1 ),
    inference(avatar_split_clause,[],[f2785,f3464])).

fof(f2785,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2583])).
%------------------------------------------------------------------------------
