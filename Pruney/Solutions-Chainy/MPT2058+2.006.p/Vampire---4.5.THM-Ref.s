%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 669 expanded)
%              Number of leaves         :   26 ( 165 expanded)
%              Depth                    :   12
%              Number of atoms          :  600 (4042 expanded)
%              Number of equality atoms :   11 (  66 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f268,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f101,f122,f126,f130,f137,f156,f164,f168,f172,f183,f187,f221,f233,f253,f259,f267])).

fof(f267,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | spl3_17 ),
    inference(unit_resulting_resolution,[],[f98,f261])).

fof(f261,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | spl3_17 ),
    inference(forward_demodulation,[],[f260,f87])).

fof(f87,plain,(
    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f71,f33,f38,f36,f35,f34,f37,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow19)).

fof(f34,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f40,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f260,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | spl3_17 ),
    inference(unit_resulting_resolution,[],[f79,f196,f200,f204,f178,f95,f121])).

fof(f121,plain,
    ( ! [X2,X3] :
        ( ~ l1_waybel_0(X2,sK0)
        | ~ r3_waybel_9(sK0,X2,X3)
        | v2_struct_0(X2)
        | r1_waybel_7(sK0,k2_yellow19(sK0,X2),X3)
        | ~ m1_subset_1(X3,k2_struct_0(sK0))
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl3_7
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X3,k2_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X2,X3)
        | v2_struct_0(X2)
        | r1_waybel_7(sK0,k2_yellow19(sK0,X2),X3)
        | ~ l1_waybel_0(X2,sK0)
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f95,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_1
  <=> r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f178,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl3_13
  <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f204,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl3_17
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f200,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl3_16
  <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f196,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl3_15
  <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f79,plain,(
    m1_subset_1(sK2,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f32,f74])).

fof(f74,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f71,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f32,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f98,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_2
  <=> r1_waybel_7(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f259,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | spl3_17 ),
    inference(unit_resulting_resolution,[],[f99,f255])).

fof(f255,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | spl3_1
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | spl3_17 ),
    inference(forward_demodulation,[],[f254,f87])).

fof(f254,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | spl3_1
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | spl3_17 ),
    inference(unit_resulting_resolution,[],[f79,f196,f200,f94,f178,f204,f136])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(X0,sK0)
        | r3_waybel_9(sK0,X0,X1)
        | v2_struct_0(X0)
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
        | ~ m1_subset_1(X1,k2_struct_0(sK0))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k2_struct_0(sK0))
        | r3_waybel_9(sK0,X0,X1)
        | v2_struct_0(X0)
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f94,plain,
    ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f99,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f253,plain,(
    ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f63,f240,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f240,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f236,f74])).

fof(f236,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f38,f71,f33,f80,f36,f35,f34,f37,f205,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).

fof(f205,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f203])).

fof(f80,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f73,f74])).

fof(f73,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f38,f71,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f233,plain,(
    spl3_16 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl3_16 ),
    inference(unit_resulting_resolution,[],[f63,f224,f60])).

fof(f224,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_16 ),
    inference(forward_demodulation,[],[f222,f74])).

fof(f222,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_16 ),
    inference(unit_resulting_resolution,[],[f38,f71,f33,f80,f36,f35,f34,f37,f201,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f201,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f199])).

fof(f221,plain,(
    spl3_15 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl3_15 ),
    inference(unit_resulting_resolution,[],[f63,f212,f60])).

fof(f212,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_15 ),
    inference(forward_demodulation,[],[f210,f74])).

fof(f210,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_15 ),
    inference(unit_resulting_resolution,[],[f38,f71,f33,f80,f36,f35,f37,f197,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).

fof(f197,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f195])).

fof(f187,plain,(
    spl3_14 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl3_14 ),
    inference(unit_resulting_resolution,[],[f63,f182,f60])).

fof(f182,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl3_14
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f183,plain,
    ( spl3_6
    | spl3_13
    | ~ spl3_14
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f174,f154,f180,f176,f116])).

fof(f116,plain,
    ( spl3_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f154,plain,
    ( spl3_12
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | l1_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1),X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f174,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(sK0)
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f173,f74])).

fof(f173,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_12 ),
    inference(resolution,[],[f155,f71])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | l1_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1),X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f172,plain,(
    ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f33,f152])).

fof(f152,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_11
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f168,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f35,f148])).

fof(f148,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_10
  <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f164,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f88,f144,f60])).

fof(f144,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl3_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f88,plain,(
    r1_tarski(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f37,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f156,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | spl3_11
    | spl3_12 ),
    inference(avatar_split_clause,[],[f140,f154,f150,f146,f142])).

fof(f140,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(sK1)
      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | l1_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1),X0) ) ),
    inference(resolution,[],[f84,f36])).

fof(f84,plain,(
    ! [X4,X5] :
      ( ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
      | v2_struct_0(X4)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X4)))
      | v1_xboole_0(X5)
      | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
      | ~ l1_struct_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | l1_waybel_0(k3_yellow19(X4,k2_struct_0(sK0),X5),X4) ) ),
    inference(resolution,[],[f80,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f137,plain,
    ( ~ spl3_5
    | spl3_6
    | spl3_8 ),
    inference(avatar_split_clause,[],[f78,f135,f116,f112])).

fof(f112,plain,
    ( spl3_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k2_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
      | r3_waybel_9(sK0,X0,X1) ) ),
    inference(backward_demodulation,[],[f69,f74])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
      | r3_waybel_9(sK0,X0,X1) ) ),
    inference(resolution,[],[f39,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f130,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f38,f118])).

fof(f118,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f126,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f40,f114])).

fof(f114,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f122,plain,
    ( ~ spl3_5
    | spl3_6
    | spl3_7 ),
    inference(avatar_split_clause,[],[f77,f120,f116,f112])).

fof(f77,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k2_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X2)
      | ~ v4_orders_2(X2)
      | ~ v7_waybel_0(X2)
      | ~ l1_waybel_0(X2,sK0)
      | r1_waybel_7(sK0,k2_yellow19(sK0,X2),X3)
      | ~ r3_waybel_9(sK0,X2,X3) ) ),
    inference(backward_demodulation,[],[f70,f74])).

fof(f70,plain,(
    ! [X2,X3] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X2)
      | ~ v4_orders_2(X2)
      | ~ v7_waybel_0(X2)
      | ~ l1_waybel_0(X2,sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_waybel_7(sK0,k2_yellow19(sK0,X2),X3)
      | ~ r3_waybel_9(sK0,X2,X3) ) ),
    inference(resolution,[],[f39,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f31,f97,f93])).

fof(f31,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f100,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f30,f97,f93])).

fof(f30,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:08:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.46  % (7950)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.47  % (7942)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.48  % (7950)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f268,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f100,f101,f122,f126,f130,f137,f156,f164,f168,f172,f183,f187,f221,f233,f253,f259,f267])).
% 0.20/0.49  fof(f267,plain,(
% 0.20/0.49    ~spl3_1 | spl3_2 | ~spl3_7 | ~spl3_13 | ~spl3_15 | ~spl3_16 | spl3_17),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f262])).
% 0.20/0.49  fof(f262,plain,(
% 0.20/0.49    $false | (~spl3_1 | spl3_2 | ~spl3_7 | ~spl3_13 | ~spl3_15 | ~spl3_16 | spl3_17)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f98,f261])).
% 0.20/0.49  fof(f261,plain,(
% 0.20/0.49    r1_waybel_7(sK0,sK1,sK2) | (~spl3_1 | ~spl3_7 | ~spl3_13 | ~spl3_15 | ~spl3_16 | spl3_17)),
% 0.20/0.49    inference(forward_demodulation,[],[f260,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f71,f33,f38,f36,f35,f34,f37,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f12])).
% 0.20/0.49  fof(f12,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow19)).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    l1_struct_0(sK0)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f40,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f260,plain,(
% 0.20/0.49    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | (~spl3_1 | ~spl3_7 | ~spl3_13 | ~spl3_15 | ~spl3_16 | spl3_17)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f79,f196,f200,f204,f178,f95,f121])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~l1_waybel_0(X2,sK0) | ~r3_waybel_9(sK0,X2,X3) | v2_struct_0(X2) | r1_waybel_7(sK0,k2_yellow19(sK0,X2),X3) | ~m1_subset_1(X3,k2_struct_0(sK0)) | ~v7_waybel_0(X2) | ~v4_orders_2(X2)) ) | ~spl3_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f120])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    spl3_7 <=> ! [X3,X2] : (~m1_subset_1(X3,k2_struct_0(sK0)) | ~r3_waybel_9(sK0,X2,X3) | v2_struct_0(X2) | r1_waybel_7(sK0,k2_yellow19(sK0,X2),X3) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f93])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    spl3_1 <=> r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~spl3_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f176])).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    spl3_13 <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl3_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f203])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    spl3_17 <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl3_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f199])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    spl3_16 <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.49  fof(f196,plain,(
% 0.20/0.49    v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl3_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f195])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    spl3_15 <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    m1_subset_1(sK2,k2_struct_0(sK0))),
% 0.20/0.49    inference(backward_demodulation,[],[f32,f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f71,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ~r1_waybel_7(sK0,sK1,sK2) | spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f97])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    spl3_2 <=> r1_waybel_7(sK0,sK1,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f259,plain,(
% 0.20/0.49    spl3_1 | ~spl3_2 | ~spl3_8 | ~spl3_13 | ~spl3_15 | ~spl3_16 | spl3_17),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f256])).
% 0.20/0.49  fof(f256,plain,(
% 0.20/0.49    $false | (spl3_1 | ~spl3_2 | ~spl3_8 | ~spl3_13 | ~spl3_15 | ~spl3_16 | spl3_17)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f99,f255])).
% 0.20/0.49  fof(f255,plain,(
% 0.20/0.49    ~r1_waybel_7(sK0,sK1,sK2) | (spl3_1 | ~spl3_8 | ~spl3_13 | ~spl3_15 | ~spl3_16 | spl3_17)),
% 0.20/0.49    inference(forward_demodulation,[],[f254,f87])).
% 0.20/0.49  fof(f254,plain,(
% 0.20/0.49    ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | (spl3_1 | ~spl3_8 | ~spl3_13 | ~spl3_15 | ~spl3_16 | spl3_17)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f79,f196,f200,f94,f178,f204,f136])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | r3_waybel_9(sK0,X0,X1) | v2_struct_0(X0) | ~r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1) | ~m1_subset_1(X1,k2_struct_0(sK0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0)) ) | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f135])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    spl3_8 <=> ! [X1,X0] : (~m1_subset_1(X1,k2_struct_0(sK0)) | r3_waybel_9(sK0,X0,X1) | v2_struct_0(X0) | ~r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f93])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    r1_waybel_7(sK0,sK1,sK2) | ~spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f97])).
% 0.20/0.49  fof(f253,plain,(
% 0.20/0.49    ~spl3_17),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f248])).
% 0.20/0.49  fof(f248,plain,(
% 0.20/0.49    $false | ~spl3_17),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f63,f240,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.49  fof(f240,plain,(
% 0.20/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_17),
% 0.20/0.49    inference(forward_demodulation,[],[f236,f74])).
% 0.20/0.49  fof(f236,plain,(
% 0.20/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_17),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f38,f71,f33,f80,f36,f35,f34,f37,f205,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).
% 0.20/0.49  fof(f205,plain,(
% 0.20/0.49    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl3_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f203])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ~v1_xboole_0(k2_struct_0(sK0))),
% 0.20/0.49    inference(forward_demodulation,[],[f73,f74])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f38,f71,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_struct_0(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f233,plain,(
% 0.20/0.49    spl3_16),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f228])).
% 0.20/0.49  fof(f228,plain,(
% 0.20/0.49    $false | spl3_16),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f63,f224,f60])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_16),
% 0.20/0.49    inference(forward_demodulation,[],[f222,f74])).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_16),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f38,f71,f33,f80,f36,f35,f34,f37,f201,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl3_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f199])).
% 0.20/0.49  fof(f221,plain,(
% 0.20/0.49    spl3_15),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f216])).
% 0.20/0.49  fof(f216,plain,(
% 0.20/0.49    $false | spl3_15),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f63,f212,f60])).
% 0.20/0.49  fof(f212,plain,(
% 0.20/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_15),
% 0.20/0.49    inference(forward_demodulation,[],[f210,f74])).
% 0.20/0.49  fof(f210,plain,(
% 0.20/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_15),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f38,f71,f33,f80,f36,f35,f37,f197,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl3_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f195])).
% 0.20/0.49  fof(f187,plain,(
% 0.20/0.49    spl3_14),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f185])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    $false | spl3_14),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f63,f182,f60])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f180])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    spl3_14 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    spl3_6 | spl3_13 | ~spl3_14 | ~spl3_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f174,f154,f180,f176,f116])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    spl3_6 <=> v2_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    spl3_12 <=> ! [X0] : (v2_struct_0(X0) | l1_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1),X0) | ~l1_struct_0(X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(sK0) | ~spl3_12),
% 0.20/0.49    inference(forward_demodulation,[],[f173,f74])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_12),
% 0.20/0.49    inference(resolution,[],[f155,f71])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_struct_0(X0) | l1_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1),X0) | v2_struct_0(X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl3_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f154])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    ~spl3_11),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f169])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    $false | ~spl3_11),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f33,f152])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    v1_xboole_0(sK1) | ~spl3_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f150])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    spl3_11 <=> v1_xboole_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    spl3_10),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f165])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    $false | spl3_10),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f35,f148])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | spl3_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f146])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    spl3_10 <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    spl3_9),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f159])).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    $false | spl3_9),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f88,f144,f60])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f142])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    spl3_9 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    r1_tarski(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f37,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f156,plain,(
% 0.20/0.49    ~spl3_9 | ~spl3_10 | spl3_11 | spl3_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f140,f154,f150,f146,f142])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~l1_struct_0(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | l1_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1),X0)) )),
% 0.20/0.49    inference(resolution,[],[f84,f36])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ( ! [X4,X5] : (~v13_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0))) | v2_struct_0(X4) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X4))) | v1_xboole_0(X5) | ~v2_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0))) | ~l1_struct_0(X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | l1_waybel_0(k3_yellow19(X4,k2_struct_0(sK0),X5),X4)) )),
% 0.20/0.49    inference(resolution,[],[f80,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | l1_waybel_0(k3_yellow19(X0,X1,X2),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    ~spl3_5 | spl3_6 | spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f78,f135,f116,f112])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    spl3_5 <=> l1_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1) | r3_waybel_9(sK0,X0,X1)) )),
% 0.20/0.49    inference(backward_demodulation,[],[f69,f74])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1) | r3_waybel_9(sK0,X0,X1)) )),
% 0.20/0.49    inference(resolution,[],[f39,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | r3_waybel_9(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    v2_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ~spl3_6),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f127])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    $false | ~spl3_6),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f38,f118])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    v2_struct_0(sK0) | ~spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f116])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    spl3_5),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f123])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    $false | spl3_5),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f40,f114])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f112])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    ~spl3_5 | spl3_6 | spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f77,f120,f116,f112])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~m1_subset_1(X3,k2_struct_0(sK0)) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,X2),X3) | ~r3_waybel_9(sK0,X2,X3)) )),
% 0.20/0.49    inference(backward_demodulation,[],[f70,f74])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X2,X3] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,X2),X3) | ~r3_waybel_9(sK0,X2,X3)) )),
% 0.20/0.49    inference(resolution,[],[f39,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f97,f93])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    spl3_1 | spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f30,f97,f93])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (7950)------------------------------
% 0.20/0.49  % (7950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (7950)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (7950)Memory used [KB]: 6396
% 0.20/0.49  % (7950)Time elapsed: 0.091 s
% 0.20/0.49  % (7950)------------------------------
% 0.20/0.49  % (7950)------------------------------
% 0.20/0.49  % (7924)Success in time 0.145 s
%------------------------------------------------------------------------------
