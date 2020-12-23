%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1285+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:16 EST 2020

% Result     : Theorem 12.68s
% Output     : Refutation 12.68s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 372 expanded)
%              Number of leaves         :   35 ( 166 expanded)
%              Depth                    :   10
%              Number of atoms          :  601 (2212 expanded)
%              Number of equality atoms :   29 (  63 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23086,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3662,f3667,f3672,f3682,f3692,f3706,f3716,f3726,f3740,f3741,f3742,f3878,f3968,f8112,f9280,f13741,f15067,f15294,f16246,f16861,f22283,f22347,f23050])).

fof(f23050,plain,
    ( ~ spl105_2
    | ~ spl105_5
    | spl105_17
    | ~ spl105_93
    | ~ spl105_110
    | ~ spl105_112
    | ~ spl105_120 ),
    inference(avatar_contradiction_clause,[],[f23049])).

fof(f23049,plain,
    ( $false
    | ~ spl105_2
    | ~ spl105_5
    | spl105_17
    | ~ spl105_93
    | ~ spl105_110
    | ~ spl105_112
    | ~ spl105_120 ),
    inference(subsumption_resolution,[],[f22938,f15293])).

fof(f15293,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl105_112 ),
    inference(avatar_component_clause,[],[f15291])).

fof(f15291,plain,
    ( spl105_112
  <=> r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_112])])).

fof(f22938,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl105_2
    | ~ spl105_5
    | spl105_17
    | ~ spl105_93
    | ~ spl105_110
    | ~ spl105_120 ),
    inference(backward_demodulation,[],[f16000,f22603])).

fof(f22603,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl105_110
    | ~ spl105_120 ),
    inference(unit_resulting_resolution,[],[f15066,f16860,f3102])).

fof(f3102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2768])).

fof(f2768,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2767])).

fof(f2767,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f16860,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK2))
    | ~ spl105_120 ),
    inference(avatar_component_clause,[],[f16858])).

fof(f16858,plain,
    ( spl105_120
  <=> r1_tarski(sK2,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_120])])).

fof(f15066,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl105_110 ),
    inference(avatar_component_clause,[],[f15064])).

fof(f15064,plain,
    ( spl105_110
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_110])])).

fof(f16000,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ spl105_2
    | ~ spl105_5
    | spl105_17
    | ~ spl105_93 ),
    inference(unit_resulting_resolution,[],[f3666,f3739,f3681,f9757,f2916])).

fof(f2916,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2674])).

fof(f2674,plain,(
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
    inference(flattening,[],[f2673])).

fof(f2673,plain,(
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
    inference(nnf_transformation,[],[f2216])).

fof(f2216,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

fof(f9757,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ spl105_93 ),
    inference(avatar_component_clause,[],[f9755])).

fof(f9755,plain,
    ( spl105_93
  <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_93])])).

fof(f3681,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl105_5 ),
    inference(avatar_component_clause,[],[f3679])).

fof(f3679,plain,
    ( spl105_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_5])])).

fof(f3739,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | spl105_17 ),
    inference(avatar_component_clause,[],[f3737])).

fof(f3737,plain,
    ( spl105_17
  <=> v4_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_17])])).

fof(f3666,plain,
    ( l1_pre_topc(sK0)
    | ~ spl105_2 ),
    inference(avatar_component_clause,[],[f3664])).

fof(f3664,plain,
    ( spl105_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_2])])).

fof(f22347,plain,
    ( ~ spl105_3
    | ~ spl105_7
    | ~ spl105_9
    | ~ spl105_84
    | spl105_133 ),
    inference(avatar_contradiction_clause,[],[f22346])).

fof(f22346,plain,
    ( $false
    | ~ spl105_3
    | ~ spl105_7
    | ~ spl105_9
    | ~ spl105_84
    | spl105_133 ),
    inference(subsumption_resolution,[],[f22288,f6298])).

fof(f6298,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl105_3
    | ~ spl105_7 ),
    inference(unit_resulting_resolution,[],[f3671,f3691,f2957])).

fof(f2957,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f2257])).

fof(f2257,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2256])).

fof(f2256,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f3691,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl105_7 ),
    inference(avatar_component_clause,[],[f3689])).

fof(f3689,plain,
    ( spl105_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_7])])).

fof(f3671,plain,
    ( l1_pre_topc(sK1)
    | ~ spl105_3 ),
    inference(avatar_component_clause,[],[f3669])).

fof(f3669,plain,
    ( spl105_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_3])])).

fof(f22288,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl105_3
    | ~ spl105_7
    | ~ spl105_9
    | ~ spl105_84
    | spl105_133 ),
    inference(unit_resulting_resolution,[],[f3671,f3701,f3691,f8111,f22282,f2948])).

fof(f2948,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f2244])).

fof(f2244,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2243])).

fof(f2243,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2164])).

fof(f2164,axiom,(
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

fof(f22282,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | spl105_133 ),
    inference(avatar_component_clause,[],[f22280])).

fof(f22280,plain,
    ( spl105_133
  <=> r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_133])])).

fof(f8111,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ spl105_84 ),
    inference(avatar_component_clause,[],[f8109])).

fof(f8109,plain,
    ( spl105_84
  <=> r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_84])])).

fof(f3701,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ spl105_9 ),
    inference(avatar_component_clause,[],[f3699])).

fof(f3699,plain,
    ( spl105_9
  <=> v3_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_9])])).

fof(f22283,plain,
    ( ~ spl105_133
    | spl105_35
    | ~ spl105_40 ),
    inference(avatar_split_clause,[],[f4545,f3965,f3875,f22280])).

fof(f3875,plain,
    ( spl105_35
  <=> sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_35])])).

fof(f3965,plain,
    ( spl105_40
  <=> r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_40])])).

fof(f4545,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | spl105_35
    | ~ spl105_40 ),
    inference(unit_resulting_resolution,[],[f3877,f3967,f3102])).

fof(f3967,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ spl105_40 ),
    inference(avatar_component_clause,[],[f3965])).

fof(f3877,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | spl105_35 ),
    inference(avatar_component_clause,[],[f3875])).

fof(f16861,plain,
    ( spl105_120
    | ~ spl105_2
    | ~ spl105_5
    | ~ spl105_16 ),
    inference(avatar_split_clause,[],[f11947,f3733,f3679,f3664,f16858])).

fof(f3733,plain,
    ( spl105_16
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_16])])).

fof(f11947,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK2))
    | ~ spl105_2
    | ~ spl105_5
    | ~ spl105_16 ),
    inference(unit_resulting_resolution,[],[f3666,f3734,f3537,f3681,f3681,f2948])).

fof(f3537,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f3101])).

fof(f3101,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2768])).

fof(f3734,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl105_16 ),
    inference(avatar_component_clause,[],[f3733])).

fof(f16246,plain,
    ( ~ spl105_10
    | ~ spl105_2
    | ~ spl105_5
    | spl105_33 ),
    inference(avatar_split_clause,[],[f12143,f3857,f3679,f3664,f3703])).

fof(f3703,plain,
    ( spl105_10
  <=> v6_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_10])])).

fof(f3857,plain,
    ( spl105_33
  <=> sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_33])])).

fof(f12143,plain,
    ( ~ v6_tops_1(sK2,sK0)
    | ~ spl105_2
    | ~ spl105_5
    | spl105_33 ),
    inference(unit_resulting_resolution,[],[f3666,f3681,f3858,f2903])).

fof(f2903,plain,(
    ! [X0,X1] :
      ( ~ v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2670])).

fof(f2670,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2208])).

fof(f2208,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2099])).

fof(f2099,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

fof(f3858,plain,
    ( sK2 != k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | spl105_33 ),
    inference(avatar_component_clause,[],[f3857])).

fof(f15294,plain,
    ( spl105_112
    | ~ spl105_2
    | ~ spl105_5 ),
    inference(avatar_split_clause,[],[f9064,f3679,f3664,f15291])).

fof(f9064,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl105_2
    | ~ spl105_5 ),
    inference(unit_resulting_resolution,[],[f3666,f3681,f2981])).

fof(f2981,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f2266])).

fof(f2266,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f15067,plain,
    ( spl105_110
    | ~ spl105_2
    | ~ spl105_5 ),
    inference(avatar_split_clause,[],[f9059,f3679,f3664,f15064])).

fof(f9059,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl105_2
    | ~ spl105_5 ),
    inference(unit_resulting_resolution,[],[f3666,f3681,f2955])).

fof(f2955,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f2253])).

fof(f2253,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2156])).

fof(f2156,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f13741,plain,
    ( ~ spl105_33
    | spl105_93 ),
    inference(avatar_contradiction_clause,[],[f13740])).

fof(f13740,plain,
    ( $false
    | ~ spl105_33
    | spl105_93 ),
    inference(subsumption_resolution,[],[f13729,f4258])).

fof(f4258,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f3537,f3535])).

fof(f3535,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f3094])).

fof(f3094,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2762])).

fof(f2762,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK30(X0,X1),X0)
            | ~ r2_hidden(sK30(X0,X1),X1) )
          & ( r1_tarski(sK30(X0,X1),X0)
            | r2_hidden(sK30(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK30])],[f2760,f2761])).

fof(f2761,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK30(X0,X1),X0)
          | ~ r2_hidden(sK30(X0,X1),X1) )
        & ( r1_tarski(sK30(X0,X1),X0)
          | r2_hidden(sK30(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2760,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f2759])).

fof(f2759,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f13729,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(sK2))
    | ~ spl105_33
    | spl105_93 ),
    inference(backward_demodulation,[],[f9787,f3859])).

fof(f3859,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl105_33 ),
    inference(avatar_component_clause,[],[f3857])).

fof(f9787,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(sK2))
    | spl105_93 ),
    inference(unit_resulting_resolution,[],[f9756,f3536])).

fof(f3536,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f3093])).

fof(f3093,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2762])).

fof(f9756,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | spl105_93 ),
    inference(avatar_component_clause,[],[f9755])).

fof(f9280,plain,
    ( ~ spl105_1
    | ~ spl105_2
    | ~ spl105_5
    | spl105_16
    | ~ spl105_33 ),
    inference(avatar_contradiction_clause,[],[f9279])).

fof(f9279,plain,
    ( $false
    | ~ spl105_1
    | ~ spl105_2
    | ~ spl105_5
    | spl105_16
    | ~ spl105_33 ),
    inference(subsumption_resolution,[],[f9278,f3661])).

fof(f3661,plain,
    ( v2_pre_topc(sK0)
    | ~ spl105_1 ),
    inference(avatar_component_clause,[],[f3659])).

fof(f3659,plain,
    ( spl105_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_1])])).

fof(f9278,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl105_2
    | ~ spl105_5
    | spl105_16
    | ~ spl105_33 ),
    inference(subsumption_resolution,[],[f9277,f3666])).

fof(f9277,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl105_2
    | ~ spl105_5
    | spl105_16
    | ~ spl105_33 ),
    inference(subsumption_resolution,[],[f9276,f9061])).

fof(f9061,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl105_2
    | ~ spl105_5 ),
    inference(unit_resulting_resolution,[],[f3666,f3681,f2957])).

fof(f9276,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl105_16
    | ~ spl105_33 ),
    inference(subsumption_resolution,[],[f9267,f3735])).

fof(f3735,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | spl105_16 ),
    inference(avatar_component_clause,[],[f3733])).

fof(f9267,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl105_33 ),
    inference(superposition,[],[f2938,f3859])).

fof(f2938,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2234])).

fof(f2234,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2233])).

fof(f2233,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2119])).

fof(f2119,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f8112,plain,
    ( spl105_84
    | ~ spl105_3
    | ~ spl105_7 ),
    inference(avatar_split_clause,[],[f5365,f3689,f3669,f8109])).

fof(f5365,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ spl105_3
    | ~ spl105_7 ),
    inference(unit_resulting_resolution,[],[f3671,f3691,f2981])).

fof(f3968,plain,
    ( spl105_40
    | ~ spl105_3
    | ~ spl105_7
    | ~ spl105_12 ),
    inference(avatar_split_clause,[],[f3954,f3713,f3689,f3669,f3965])).

fof(f3713,plain,
    ( spl105_12
  <=> v4_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_12])])).

fof(f3954,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ spl105_3
    | ~ spl105_7
    | ~ spl105_12 ),
    inference(unit_resulting_resolution,[],[f3671,f3691,f3715,f2914])).

fof(f2914,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2674])).

fof(f3715,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ spl105_12 ),
    inference(avatar_component_clause,[],[f3713])).

fof(f3878,plain,
    ( ~ spl105_35
    | ~ spl105_3
    | ~ spl105_7
    | spl105_14 ),
    inference(avatar_split_clause,[],[f3784,f3723,f3689,f3669,f3875])).

fof(f3723,plain,
    ( spl105_14
  <=> v6_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl105_14])])).

fof(f3784,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ spl105_3
    | ~ spl105_7
    | spl105_14 ),
    inference(unit_resulting_resolution,[],[f3671,f3725,f3691,f2904])).

fof(f2904,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2670])).

fof(f3725,plain,
    ( ~ v6_tops_1(sK3,sK1)
    | spl105_14 ),
    inference(avatar_component_clause,[],[f3723])).

fof(f3742,plain,
    ( ~ spl105_14
    | ~ spl105_16
    | ~ spl105_17 ),
    inference(avatar_split_clause,[],[f2902,f3737,f3733,f3723])).

fof(f2902,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f2669])).

fof(f2669,plain,
    ( ( ( ( ~ v4_tops_1(sK2,sK0)
          | ~ v3_pre_topc(sK2,sK0) )
        & v6_tops_1(sK2,sK0) )
      | ( ~ v6_tops_1(sK3,sK1)
        & v4_tops_1(sK3,sK1)
        & v3_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2207,f2668,f2667,f2666,f2665])).

fof(f2665,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v3_pre_topc(X2,X0) )
                        & v6_tops_1(X2,X0) )
                      | ( ~ v6_tops_1(X3,X1)
                        & v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK0)
                        | ~ v3_pre_topc(X2,sK0) )
                      & v6_tops_1(X2,sK0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2666,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,sK0)
                      | ~ v3_pre_topc(X2,sK0) )
                    & v6_tops_1(X2,sK0) )
                  | ( ~ v6_tops_1(X3,X1)
                    & v4_tops_1(X3,X1)
                    & v3_pre_topc(X3,X1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,sK0)
                    | ~ v3_pre_topc(X2,sK0) )
                  & v6_tops_1(X2,sK0) )
                | ( ~ v6_tops_1(X3,sK1)
                  & v4_tops_1(X3,sK1)
                  & v3_pre_topc(X3,sK1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f2667,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(X2,sK0)
                  | ~ v3_pre_topc(X2,sK0) )
                & v6_tops_1(X2,sK0) )
              | ( ~ v6_tops_1(X3,sK1)
                & v4_tops_1(X3,sK1)
                & v3_pre_topc(X3,sK1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(sK2,sK0)
                | ~ v3_pre_topc(sK2,sK0) )
              & v6_tops_1(sK2,sK0) )
            | ( ~ v6_tops_1(X3,sK1)
              & v4_tops_1(X3,sK1)
              & v3_pre_topc(X3,sK1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2668,plain,
    ( ? [X3] :
        ( ( ( ( ~ v4_tops_1(sK2,sK0)
              | ~ v3_pre_topc(sK2,sK0) )
            & v6_tops_1(sK2,sK0) )
          | ( ~ v6_tops_1(X3,sK1)
            & v4_tops_1(X3,sK1)
            & v3_pre_topc(X3,sK1) ) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ( ( ~ v4_tops_1(sK2,sK0)
            | ~ v3_pre_topc(sK2,sK0) )
          & v6_tops_1(sK2,sK0) )
        | ( ~ v6_tops_1(sK3,sK1)
          & v4_tops_1(sK3,sK1)
          & v3_pre_topc(sK3,sK1) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f2207,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2206])).

fof(f2206,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2140])).

fof(f2140,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v6_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v3_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v3_pre_topc(X3,X1) )
                       => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2139])).

fof(f2139,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v6_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v3_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) )
                     => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_tops_1)).

fof(f3741,plain,
    ( spl105_12
    | ~ spl105_16
    | ~ spl105_17 ),
    inference(avatar_split_clause,[],[f2901,f3737,f3733,f3713])).

fof(f2901,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f2669])).

fof(f3740,plain,
    ( spl105_9
    | ~ spl105_16
    | ~ spl105_17 ),
    inference(avatar_split_clause,[],[f2900,f3737,f3733,f3699])).

fof(f2900,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f2669])).

fof(f3726,plain,
    ( ~ spl105_14
    | spl105_10 ),
    inference(avatar_split_clause,[],[f2899,f3703,f3723])).

fof(f2899,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f2669])).

fof(f3716,plain,
    ( spl105_12
    | spl105_10 ),
    inference(avatar_split_clause,[],[f2898,f3703,f3713])).

fof(f2898,plain,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f2669])).

fof(f3706,plain,
    ( spl105_9
    | spl105_10 ),
    inference(avatar_split_clause,[],[f2897,f3703,f3699])).

fof(f2897,plain,
    ( v6_tops_1(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f2669])).

fof(f3692,plain,(
    spl105_7 ),
    inference(avatar_split_clause,[],[f2896,f3689])).

fof(f2896,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f2669])).

fof(f3682,plain,(
    spl105_5 ),
    inference(avatar_split_clause,[],[f2895,f3679])).

fof(f2895,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2669])).

fof(f3672,plain,(
    spl105_3 ),
    inference(avatar_split_clause,[],[f2894,f3669])).

fof(f2894,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f2669])).

fof(f3667,plain,(
    spl105_2 ),
    inference(avatar_split_clause,[],[f2893,f3664])).

fof(f2893,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2669])).

fof(f3662,plain,(
    spl105_1 ),
    inference(avatar_split_clause,[],[f2892,f3659])).

fof(f2892,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2669])).
%------------------------------------------------------------------------------
