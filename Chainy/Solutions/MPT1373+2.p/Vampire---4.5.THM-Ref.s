%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1373+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:19 EST 2020

% Result     : Theorem 8.50s
% Output     : Refutation 8.50s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 252 expanded)
%              Number of leaves         :   23 ( 103 expanded)
%              Depth                    :   11
%              Number of atoms          :  411 (1559 expanded)
%              Number of equality atoms :   40 ( 184 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14439,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5597,f5602,f5617,f5627,f5641,f5647,f5665,f5945,f6156,f11642,f14306,f14429])).

fof(f14429,plain,
    ( ~ spl373_39
    | spl373_45
    | ~ spl373_109 ),
    inference(avatar_contradiction_clause,[],[f14428])).

fof(f14428,plain,
    ( $false
    | ~ spl373_39
    | spl373_45
    | ~ spl373_109 ),
    inference(subsumption_resolution,[],[f14353,f5092])).

fof(f5092,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f3908])).

fof(f3908,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3364])).

fof(f3364,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f3363])).

fof(f3363,plain,(
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

fof(f14353,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ spl373_39
    | spl373_45
    | ~ spl373_109 ),
    inference(backward_demodulation,[],[f12291,f14338])).

fof(f14338,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl373_109 ),
    inference(unit_resulting_resolution,[],[f14305,f3960])).

fof(f3960,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2610])).

fof(f2610,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f14305,plain,
    ( l1_struct_0(sK3)
    | ~ spl373_109 ),
    inference(avatar_component_clause,[],[f14303])).

fof(f14303,plain,
    ( spl373_109
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl373_109])])).

fof(f12291,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),k2_struct_0(sK3))
    | ~ spl373_39
    | spl373_45 ),
    inference(unit_resulting_resolution,[],[f5944,f6155,f3896])).

fof(f3896,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f2562])).

fof(f2562,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2561])).

fof(f2561,plain,(
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

fof(f6155,plain,
    ( ~ r1_tarski(sK4,k2_struct_0(sK3))
    | spl373_45 ),
    inference(avatar_component_clause,[],[f6153])).

fof(f6153,plain,
    ( spl373_45
  <=> r1_tarski(sK4,k2_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl373_45])])).

fof(f5944,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3))
    | ~ spl373_39 ),
    inference(avatar_component_clause,[],[f5942])).

fof(f5942,plain,
    ( spl373_39
  <=> r1_tarski(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl373_39])])).

fof(f14306,plain,
    ( spl373_109
    | ~ spl373_14 ),
    inference(avatar_split_clause,[],[f14033,f5662,f14303])).

fof(f5662,plain,
    ( spl373_14
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl373_14])])).

fof(f14033,plain,
    ( l1_struct_0(sK3)
    | ~ spl373_14 ),
    inference(unit_resulting_resolution,[],[f5664,f4626])).

fof(f4626,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2989])).

fof(f2989,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f5664,plain,
    ( l1_pre_topc(sK3)
    | ~ spl373_14 ),
    inference(avatar_component_clause,[],[f5662])).

fof(f11642,plain,
    ( ~ spl373_1
    | ~ spl373_2
    | ~ spl373_5
    | spl373_9
    | ~ spl373_10
    | ~ spl373_45 ),
    inference(avatar_contradiction_clause,[],[f11641])).

fof(f11641,plain,
    ( $false
    | ~ spl373_1
    | ~ spl373_2
    | ~ spl373_5
    | spl373_9
    | ~ spl373_10
    | ~ spl373_45 ),
    inference(subsumption_resolution,[],[f11640,f5640])).

fof(f5640,plain,
    ( v2_compts_1(sK4,sK3)
    | ~ spl373_10 ),
    inference(avatar_component_clause,[],[f5638])).

fof(f5638,plain,
    ( spl373_10
  <=> v2_compts_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl373_10])])).

fof(f11640,plain,
    ( ~ v2_compts_1(sK4,sK3)
    | ~ spl373_1
    | ~ spl373_2
    | ~ spl373_5
    | spl373_9
    | ~ spl373_45 ),
    inference(forward_demodulation,[],[f11607,f11608])).

fof(f11608,plain,
    ( sK4 = sK6(sK3,sK4)
    | ~ spl373_1
    | ~ spl373_2
    | ~ spl373_5
    | spl373_9
    | ~ spl373_45 ),
    inference(unit_resulting_resolution,[],[f5596,f5601,f5635,f5616,f6154,f3844])).

fof(f3844,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_struct_0(X1))
      | sK6(X1,X2) = X2
      | v2_compts_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3320])).

fof(f3320,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ( ~ v2_compts_1(sK6(X1,X2),X1)
                    & sK6(X1,X2) = X2
                    & m1_subset_1(sK6(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f3318,f3319])).

fof(f3319,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK6(X1,X2),X1)
        & sK6(X1,X2) = X2
        & m1_subset_1(sK6(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f3318,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f3317])).

fof(f3317,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v2_compts_1(X3,X1)
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2521])).

fof(f2521,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2520])).

fof(f2520,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2470])).

fof(f2470,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

fof(f6154,plain,
    ( r1_tarski(sK4,k2_struct_0(sK3))
    | ~ spl373_45 ),
    inference(avatar_component_clause,[],[f6153])).

fof(f5616,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl373_5 ),
    inference(avatar_component_clause,[],[f5614])).

fof(f5614,plain,
    ( spl373_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl373_5])])).

fof(f5635,plain,
    ( ~ v2_compts_1(sK4,sK2)
    | spl373_9 ),
    inference(avatar_component_clause,[],[f5634])).

fof(f5634,plain,
    ( spl373_9
  <=> v2_compts_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl373_9])])).

fof(f5601,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl373_2 ),
    inference(avatar_component_clause,[],[f5599])).

fof(f5599,plain,
    ( spl373_2
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl373_2])])).

fof(f5596,plain,
    ( l1_pre_topc(sK2)
    | ~ spl373_1 ),
    inference(avatar_component_clause,[],[f5594])).

fof(f5594,plain,
    ( spl373_1
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl373_1])])).

fof(f11607,plain,
    ( ~ v2_compts_1(sK6(sK3,sK4),sK3)
    | ~ spl373_1
    | ~ spl373_2
    | ~ spl373_5
    | spl373_9
    | ~ spl373_45 ),
    inference(unit_resulting_resolution,[],[f5596,f5601,f5635,f5616,f6154,f3845])).

fof(f3845,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_compts_1(sK6(X1,X2),X1)
      | v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3320])).

fof(f6156,plain,
    ( ~ spl373_45
    | ~ spl373_1
    | ~ spl373_2
    | ~ spl373_5
    | ~ spl373_7
    | ~ spl373_9
    | spl373_10 ),
    inference(avatar_split_clause,[],[f6121,f5638,f5634,f5624,f5614,f5599,f5594,f6153])).

fof(f5624,plain,
    ( spl373_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl373_7])])).

fof(f6121,plain,
    ( ~ r1_tarski(sK4,k2_struct_0(sK3))
    | ~ spl373_1
    | ~ spl373_2
    | ~ spl373_5
    | ~ spl373_7
    | ~ spl373_9
    | spl373_10 ),
    inference(unit_resulting_resolution,[],[f5596,f5601,f5636,f5616,f5626,f5639,f5082])).

fof(f5082,plain,(
    ! [X4,X0,X1] :
      ( ~ r1_tarski(X4,k2_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X4,X0)
      | v2_compts_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f3842])).

fof(f3842,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_compts_1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3320])).

fof(f5639,plain,
    ( ~ v2_compts_1(sK4,sK3)
    | spl373_10 ),
    inference(avatar_component_clause,[],[f5638])).

fof(f5626,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl373_7 ),
    inference(avatar_component_clause,[],[f5624])).

fof(f5636,plain,
    ( v2_compts_1(sK4,sK2)
    | ~ spl373_9 ),
    inference(avatar_component_clause,[],[f5634])).

fof(f5945,plain,
    ( spl373_39
    | ~ spl373_7 ),
    inference(avatar_split_clause,[],[f5895,f5624,f5942])).

fof(f5895,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3))
    | ~ spl373_7 ),
    inference(unit_resulting_resolution,[],[f5626,f3898])).

fof(f3898,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3354])).

fof(f3354,plain,(
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

fof(f5665,plain,
    ( spl373_14
    | ~ spl373_1
    | ~ spl373_2 ),
    inference(avatar_split_clause,[],[f5660,f5599,f5594,f5662])).

fof(f5660,plain,
    ( l1_pre_topc(sK3)
    | ~ spl373_1
    | ~ spl373_2 ),
    inference(unit_resulting_resolution,[],[f5601,f5596,f3871])).

fof(f3871,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f2540])).

fof(f2540,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f5647,plain,
    ( ~ spl373_9
    | ~ spl373_10 ),
    inference(avatar_split_clause,[],[f5522,f5638,f5634])).

fof(f5522,plain,
    ( ~ v2_compts_1(sK4,sK3)
    | ~ v2_compts_1(sK4,sK2) ),
    inference(backward_demodulation,[],[f3832,f3830])).

fof(f3830,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f3315])).

fof(f3315,plain,
    ( ( ~ v2_compts_1(sK5,sK3)
      | ~ v2_compts_1(sK4,sK2) )
    & ( v2_compts_1(sK5,sK3)
      | v2_compts_1(sK4,sK2) )
    & sK4 = sK5
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_pre_topc(sK3,sK2)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f3310,f3314,f3313,f3312,f3311])).

fof(f3311,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v2_compts_1(X3,X1)
                      | ~ v2_compts_1(X2,X0) )
                    & ( v2_compts_1(X3,X1)
                      | v2_compts_1(X2,X0) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,sK2) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,sK2) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_pre_topc(X1,sK2) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3312,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v2_compts_1(X3,X1)
                  | ~ v2_compts_1(X2,sK2) )
                & ( v2_compts_1(X3,X1)
                  | v2_compts_1(X2,sK2) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_pre_topc(X1,sK2) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v2_compts_1(X3,sK3)
                | ~ v2_compts_1(X2,sK2) )
              & ( v2_compts_1(X3,sK3)
                | v2_compts_1(X2,sK2) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_pre_topc(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3313,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v2_compts_1(X3,sK3)
              | ~ v2_compts_1(X2,sK2) )
            & ( v2_compts_1(X3,sK3)
              | v2_compts_1(X2,sK2) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X3] :
          ( ( ~ v2_compts_1(X3,sK3)
            | ~ v2_compts_1(sK4,sK2) )
          & ( v2_compts_1(X3,sK3)
            | v2_compts_1(sK4,sK2) )
          & sK4 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f3314,plain,
    ( ? [X3] :
        ( ( ~ v2_compts_1(X3,sK3)
          | ~ v2_compts_1(sK4,sK2) )
        & ( v2_compts_1(X3,sK3)
          | v2_compts_1(sK4,sK2) )
        & sK4 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ( ~ v2_compts_1(sK5,sK3)
        | ~ v2_compts_1(sK4,sK2) )
      & ( v2_compts_1(sK5,sK3)
        | v2_compts_1(sK4,sK2) )
      & sK4 = sK5
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f3310,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,X0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,X0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3309])).

fof(f3309,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,X0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,X0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2507])).

fof(f2507,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <~> v2_compts_1(X3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2506])).

fof(f2506,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <~> v2_compts_1(X3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2490])).

fof(f2490,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( v2_compts_1(X2,X0)
                      <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2489])).

fof(f2489,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_compts_1(X2,X0)
                    <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).

fof(f3832,plain,
    ( ~ v2_compts_1(sK5,sK3)
    | ~ v2_compts_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f3315])).

fof(f5641,plain,
    ( spl373_9
    | spl373_10 ),
    inference(avatar_split_clause,[],[f5521,f5638,f5634])).

fof(f5521,plain,
    ( v2_compts_1(sK4,sK3)
    | v2_compts_1(sK4,sK2) ),
    inference(backward_demodulation,[],[f3831,f3830])).

fof(f3831,plain,
    ( v2_compts_1(sK5,sK3)
    | v2_compts_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f3315])).

fof(f5627,plain,(
    spl373_7 ),
    inference(avatar_split_clause,[],[f5523,f5624])).

fof(f5523,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_demodulation,[],[f3829,f3830])).

fof(f3829,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f3315])).

fof(f5617,plain,(
    spl373_5 ),
    inference(avatar_split_clause,[],[f3828,f5614])).

fof(f3828,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f3315])).

fof(f5602,plain,(
    spl373_2 ),
    inference(avatar_split_clause,[],[f3827,f5599])).

fof(f3827,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f3315])).

fof(f5597,plain,(
    spl373_1 ),
    inference(avatar_split_clause,[],[f3826,f5594])).

fof(f3826,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f3315])).
%------------------------------------------------------------------------------
