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
% DateTime   : Thu Dec  3 13:10:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 354 expanded)
%              Number of leaves         :   23 ( 143 expanded)
%              Depth                    :   18
%              Number of atoms          :  903 (1743 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f368,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f67,f95,f100,f105,f110,f118,f131,f143,f209,f217,f230,f235,f291,f367])).

fof(f367,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_17
    | ~ spl5_19
    | ~ spl5_24 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_17
    | ~ spl5_19
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f365,f117])).

fof(f117,plain,
    ( ~ r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl5_10
  <=> r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f365,plain,
    ( r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_17
    | ~ spl5_19
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f364,f130])).

fof(f130,plain,
    ( m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl5_11
  <=> m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f364,plain,
    ( ~ m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_17
    | ~ spl5_19
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f363,f109])).

fof(f109,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f363,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_17
    | ~ spl5_19
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f358,f229])).

fof(f229,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl5_19
  <=> r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f358,plain,
    ( ~ r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | ~ spl5_17
    | ~ spl5_24 ),
    inference(resolution,[],[f297,f150])).

fof(f150,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),X3),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k3_orders_2(sK0,sK3,sK1),X3) )
    | ~ spl5_12 ),
    inference(resolution,[],[f142,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f142,plain,
    ( m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl5_12
  <=> m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f297,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,X1,sK2))
        | ~ r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_17
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f296,f208])).

fof(f208,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl5_17
  <=> m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f296,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),X1)
        | r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,X1,sK2)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f293,f99])).

fof(f99,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_7
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f293,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),X1)
        | r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,X1,sK2)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_24 ),
    inference(resolution,[],[f290,f164])).

fof(f164,plain,
    ( ! [X14,X15,X16] :
        ( ~ r2_orders_2(sK0,X14,X15)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ r2_hidden(X14,X16)
        | r2_hidden(X14,k3_orders_2(sK0,X16,X15)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f87,f66])).

fof(f66,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f87,plain,
    ( ! [X14,X15,X16] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X14,X15)
        | ~ r2_hidden(X14,X16)
        | r2_hidden(X14,k3_orders_2(sK0,X16,X15)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f86,f46])).

fof(f46,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f86,plain,
    ( ! [X14,X15,X16] :
        ( v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X14,X15)
        | ~ r2_hidden(X14,X16)
        | r2_hidden(X14,k3_orders_2(sK0,X16,X15)) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f85,f56])).

fof(f56,plain,
    ( v4_orders_2(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f85,plain,
    ( ! [X14,X15,X16] :
        ( ~ v4_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X14,X15)
        | ~ r2_hidden(X14,X16)
        | r2_hidden(X14,k3_orders_2(sK0,X16,X15)) )
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f73,f51])).

fof(f51,plain,
    ( v3_orders_2(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f73,plain,
    ( ! [X14,X15,X16] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X14,X15)
        | ~ r2_hidden(X14,X16)
        | r2_hidden(X14,k3_orders_2(sK0,X16,X15)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f61,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(f61,plain,
    ( v5_orders_2(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f290,plain,
    ( r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl5_24
  <=> r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f291,plain,
    ( spl5_24
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_17
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f286,f232,f206,f102,f97,f92,f64,f59,f54,f288])).

fof(f92,plain,
    ( spl5_6
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f102,plain,
    ( spl5_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f232,plain,
    ( spl5_20
  <=> r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f286,plain,
    ( r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_17
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f285,f99])).

fof(f285,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_17
    | ~ spl5_20 ),
    inference(resolution,[],[f239,f94])).

fof(f94,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ r2_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),X0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_17
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f238,f104])).

fof(f104,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,sK1,X0)
        | r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0)) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_17
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f236,f208])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,sK1,X0)
        | r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0)) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(resolution,[],[f234,f133])).

fof(f133,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_orders_2(sK0,X2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,X0,X1)
        | r2_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,X0,X1)
        | r2_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,X2,X0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(resolution,[],[f126,f88])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,X0,X1) )
    | ~ spl5_5 ),
    inference(resolution,[],[f66,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f126,plain,
    ( ! [X4,X2,X3] :
        ( ~ r1_orders_2(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,X3,X4)
        | r2_orders_2(sK0,X2,X4) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f77,f66])).

fof(f77,plain,
    ( ! [X4,X2,X3] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ r2_orders_2(sK0,X3,X4)
        | r2_orders_2(sK0,X2,X4) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f69,f56])).

fof(f69,plain,
    ( ! [X4,X2,X3] :
        ( ~ v4_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ r2_orders_2(sK0,X3,X4)
        | r2_orders_2(sK0,X2,X4) )
    | ~ spl5_4 ),
    inference(resolution,[],[f61,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X2,X3)
      | r2_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ( ( ~ r2_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ( ( ~ r2_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_orders_2)).

fof(f234,plain,
    ( r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f232])).

fof(f235,plain,
    ( spl5_20
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f222,f214,f206,f107,f102,f64,f59,f54,f49,f44,f232])).

fof(f214,plain,
    ( spl5_18
  <=> r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f222,plain,
    ( r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f221,f208])).

fof(f221,plain,
    ( r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1)
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f220,f109])).

fof(f220,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1)
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f218,f104])).

fof(f218,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1)
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_18 ),
    inference(resolution,[],[f216,f154])).

fof(f154,plain,
    ( ! [X10,X8,X9] :
        ( ~ r2_hidden(X8,k3_orders_2(sK0,X10,X9))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X8,X9)
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f81,f66])).

fof(f81,plain,
    ( ! [X10,X8,X9] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X8,X9)
        | ~ r2_hidden(X8,k3_orders_2(sK0,X10,X9)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f80,f46])).

fof(f80,plain,
    ( ! [X10,X8,X9] :
        ( v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X8,X9)
        | ~ r2_hidden(X8,k3_orders_2(sK0,X10,X9)) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f79,f56])).

fof(f79,plain,
    ( ! [X10,X8,X9] :
        ( ~ v4_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X8,X9)
        | ~ r2_hidden(X8,k3_orders_2(sK0,X10,X9)) )
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f71,f51])).

fof(f71,plain,
    ( ! [X10,X8,X9] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X8,X9)
        | ~ r2_hidden(X8,k3_orders_2(sK0,X10,X9)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f61,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f216,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,sK3,sK1))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f214])).

fof(f230,plain,
    ( spl5_19
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f225,f214,f206,f107,f102,f64,f59,f54,f49,f44,f227])).

fof(f225,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f224,f208])).

fof(f224,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f223,f109])).

fof(f223,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f219,f104])).

fof(f219,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_18 ),
    inference(resolution,[],[f216,f146])).

fof(f146,plain,
    ( ! [X12,X13,X11] :
        ( ~ r2_hidden(X11,k3_orders_2(sK0,X13,X12))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X11,X13)
        | ~ m1_subset_1(X11,u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f84,f66])).

fof(f84,plain,
    ( ! [X12,X13,X11] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X11,X13)
        | ~ r2_hidden(X11,k3_orders_2(sK0,X13,X12)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f83,f46])).

fof(f83,plain,
    ( ! [X12,X13,X11] :
        ( v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X11,X13)
        | ~ r2_hidden(X11,k3_orders_2(sK0,X13,X12)) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f82,f56])).

fof(f82,plain,
    ( ! [X12,X13,X11] :
        ( ~ v4_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X11,X13)
        | ~ r2_hidden(X11,k3_orders_2(sK0,X13,X12)) )
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f72,f51])).

fof(f72,plain,
    ( ! [X12,X13,X11] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X11,X13)
        | ~ r2_hidden(X11,k3_orders_2(sK0,X13,X12)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f61,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f217,plain,
    ( spl5_18
    | spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f204,f140,f128,f115,f214])).

fof(f204,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,sK3,sK1))
    | spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f203,f130])).

fof(f203,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,sK3,sK1))
    | ~ m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_10
    | ~ spl5_12 ),
    inference(resolution,[],[f149,f117])).

fof(f149,plain,
    ( ! [X2] :
        ( r1_tarski(k3_orders_2(sK0,sK3,sK1),X2)
        | r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),X2),k3_orders_2(sK0,sK3,sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_12 ),
    inference(resolution,[],[f142,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f209,plain,
    ( spl5_17
    | spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f198,f140,f128,f115,f206])).

fof(f198,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f197,f130])).

fof(f197,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_10
    | ~ spl5_12 ),
    inference(resolution,[],[f148,f117])).

fof(f148,plain,
    ( ! [X1] :
        ( r1_tarski(k3_orders_2(sK0,sK3,sK1),X1)
        | m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_12 ),
    inference(resolution,[],[f142,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK4(X0,X1,X2),X0)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f143,plain,
    ( spl5_12
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f124,f107,f102,f64,f59,f54,f49,f44,f140])).

fof(f124,plain,
    ( m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(resolution,[],[f122,f104])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(k3_orders_2(sK0,sK3,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(resolution,[],[f121,f109])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f76,f66])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f75,f46])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f74,f56])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f68,f51])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f61,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f131,plain,
    ( spl5_11
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f123,f107,f97,f64,f59,f54,f49,f44,f128])).

fof(f123,plain,
    ( m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(resolution,[],[f122,f99])).

fof(f118,plain,(
    ~ spl5_10 ),
    inference(avatar_split_clause,[],[f21,f115])).

fof(f21,plain,(
    ~ r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2))
                  & r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2))
                  & r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( r2_orders_2(X0,X1,X2)
                     => r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_orders_2(X0,X1,X2)
                   => r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_orders_2)).

fof(f110,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f19,f107])).

fof(f19,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f105,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f23,f102])).

fof(f23,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f100,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f22,f97])).

fof(f22,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f20,f92])).

fof(f20,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f67,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f24,f44])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:21:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (1821)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (1825)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (1819)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (1829)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (1817)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (1830)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (1818)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (1820)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (1815)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (1822)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (1831)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (1816)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (1816)Refutation not found, incomplete strategy% (1816)------------------------------
% 0.21/0.50  % (1816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1816)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1816)Memory used [KB]: 10618
% 0.21/0.50  % (1816)Time elapsed: 0.073 s
% 0.21/0.50  % (1816)------------------------------
% 0.21/0.50  % (1816)------------------------------
% 0.21/0.50  % (1818)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f368,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f67,f95,f100,f105,f110,f118,f131,f143,f209,f217,f230,f235,f291,f367])).
% 0.21/0.50  fof(f367,plain,(
% 0.21/0.50    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_9 | spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_17 | ~spl5_19 | ~spl5_24),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f366])).
% 0.21/0.50  fof(f366,plain,(
% 0.21/0.50    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_9 | spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_17 | ~spl5_19 | ~spl5_24)),
% 0.21/0.50    inference(subsumption_resolution,[],[f365,f117])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ~r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)) | spl5_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl5_10 <=> r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.50  fof(f365,plain,(
% 0.21/0.50    r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_11 | ~spl5_12 | ~spl5_17 | ~spl5_19 | ~spl5_24)),
% 0.21/0.50    inference(subsumption_resolution,[],[f364,f130])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f128])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    spl5_11 <=> m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.50  fof(f364,plain,(
% 0.21/0.50    ~m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_12 | ~spl5_17 | ~spl5_19 | ~spl5_24)),
% 0.21/0.50    inference(subsumption_resolution,[],[f363,f109])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f107])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    spl5_9 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.50  fof(f363,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_12 | ~spl5_17 | ~spl5_19 | ~spl5_24)),
% 0.21/0.50    inference(subsumption_resolution,[],[f358,f229])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3) | ~spl5_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f227])).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    spl5_19 <=> r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.50  fof(f358,plain,(
% 0.21/0.50    ~r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_12 | ~spl5_17 | ~spl5_24)),
% 0.21/0.50    inference(resolution,[],[f297,f150])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ( ! [X3] : (~r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k3_orders_2(sK0,sK3,sK1),X3)) ) | ~spl5_12),
% 0.21/0.50    inference(resolution,[],[f142,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(sK4(X0,X1,X2),X2) | r1_tarski(X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f140])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    spl5_12 <=> m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.50  fof(f297,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,X1,sK2)) | ~r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_17 | ~spl5_24)),
% 0.21/0.50    inference(subsumption_resolution,[],[f296,f208])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0)) | ~spl5_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f206])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    spl5_17 <=> m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0)) | ~r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),X1) | r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,X1,sK2))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_24)),
% 0.21/0.50    inference(subsumption_resolution,[],[f293,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl5_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl5_7 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.50  fof(f293,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0)) | ~r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),X1) | r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,X1,sK2))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_24)),
% 0.21/0.50    inference(resolution,[],[f290,f164])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ( ! [X14,X15,X16] : (~r2_orders_2(sK0,X14,X15) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X14,u1_struct_0(sK0)) | ~r2_hidden(X14,X16) | r2_hidden(X14,k3_orders_2(sK0,X16,X15))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f87,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    l1_orders_2(sK0) | ~spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    spl5_5 <=> l1_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X14,X15,X16] : (~l1_orders_2(sK0) | ~m1_subset_1(X14,u1_struct_0(sK0)) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X14,X15) | ~r2_hidden(X14,X16) | r2_hidden(X14,k3_orders_2(sK0,X16,X15))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f86,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ~v2_struct_0(sK0) | spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    spl5_1 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X14,X15,X16] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X14,u1_struct_0(sK0)) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X14,X15) | ~r2_hidden(X14,X16) | r2_hidden(X14,k3_orders_2(sK0,X16,X15))) ) | (~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f85,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    v4_orders_2(sK0) | ~spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    spl5_3 <=> v4_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X14,X15,X16] : (~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X14,u1_struct_0(sK0)) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X14,X15) | ~r2_hidden(X14,X16) | r2_hidden(X14,k3_orders_2(sK0,X16,X15))) ) | (~spl5_2 | ~spl5_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f73,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    v3_orders_2(sK0) | ~spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    spl5_2 <=> v3_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X14,X15,X16] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X14,u1_struct_0(sK0)) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X14,X15) | ~r2_hidden(X14,X16) | r2_hidden(X14,k3_orders_2(sK0,X16,X15))) ) | ~spl5_4),
% 0.21/0.50    inference(resolution,[],[f61,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,X3) | r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    v5_orders_2(sK0) | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    spl5_4 <=> v5_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f290,plain,(
% 0.21/0.50    r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2) | ~spl5_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f288])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    spl5_24 <=> r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    spl5_24 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_17 | ~spl5_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f286,f232,f206,f102,f97,f92,f64,f59,f54,f288])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl5_6 <=> r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl5_8 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    spl5_20 <=> r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.50  fof(f286,plain,(
% 0.21/0.50    r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_17 | ~spl5_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f285,f99])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,u1_struct_0(sK0)) | r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_17 | ~spl5_20)),
% 0.21/0.50    inference(resolution,[],[f239,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    r2_orders_2(sK0,sK1,sK2) | ~spl5_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f92])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),X0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_17 | ~spl5_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f238,f104])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK1,X0) | r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),X0) | ~m1_subset_1(sK1,u1_struct_0(sK0))) ) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_17 | ~spl5_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f236,f208])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK1,X0) | r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),X0) | ~m1_subset_1(sK1,u1_struct_0(sK0))) ) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_20)),
% 0.21/0.50    inference(resolution,[],[f234,f133])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_orders_2(sK0,X2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X0,X1) | r2_orders_2(sK0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f132])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X0,X1) | r2_orders_2(sK0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X2,X0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(resolution,[],[f126,f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X0,X1)) ) | ~spl5_5),
% 0.21/0.50    inference(resolution,[],[f66,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~r2_orders_2(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ( ! [X4,X2,X3] : (~r1_orders_2(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X3,X4) | r2_orders_2(sK0,X2,X4)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f77,f66])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X4,X2,X3] : (~l1_orders_2(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X3) | ~r2_orders_2(sK0,X3,X4) | r2_orders_2(sK0,X2,X4)) ) | (~spl5_3 | ~spl5_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f69,f56])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X4,X2,X3] : (~v4_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X3) | ~r2_orders_2(sK0,X3,X4) | r2_orders_2(sK0,X2,X4)) ) | ~spl5_4),
% 0.21/0.50    inference(resolution,[],[f61,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~v4_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~r2_orders_2(X0,X2,X3) | r2_orders_2(X0,X1,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_orders_2(X0,X1,X3) | ((~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_orders_2(X0,X1,X3) | ((~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2)))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) => r2_orders_2(X0,X1,X3))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_orders_2)).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1) | ~spl5_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f232])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    spl5_20 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_9 | ~spl5_17 | ~spl5_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f222,f214,f206,f107,f102,f64,f59,f54,f49,f44,f232])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    spl5_18 <=> r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,sK3,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_9 | ~spl5_17 | ~spl5_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f221,f208])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1) | ~m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_9 | ~spl5_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f220,f109])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1) | ~m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f218,f104])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1) | ~m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_18)),
% 0.21/0.50    inference(resolution,[],[f216,f154])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    ( ! [X10,X8,X9] : (~r2_hidden(X8,k3_orders_2(sK0,X10,X9)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X8,X9) | ~m1_subset_1(X8,u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f81,f66])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X10,X8,X9] : (~l1_orders_2(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X8,X9) | ~r2_hidden(X8,k3_orders_2(sK0,X10,X9))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f80,f46])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X10,X8,X9] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X8,X9) | ~r2_hidden(X8,k3_orders_2(sK0,X10,X9))) ) | (~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f79,f56])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X10,X8,X9] : (~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X8,X9) | ~r2_hidden(X8,k3_orders_2(sK0,X10,X9))) ) | (~spl5_2 | ~spl5_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f71,f51])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X10,X8,X9] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X8,X9) | ~r2_hidden(X8,k3_orders_2(sK0,X10,X9))) ) | ~spl5_4),
% 0.21/0.50    inference(resolution,[],[f61,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,sK3,sK1)) | ~spl5_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f214])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    spl5_19 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_9 | ~spl5_17 | ~spl5_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f225,f214,f206,f107,f102,f64,f59,f54,f49,f44,f227])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_9 | ~spl5_17 | ~spl5_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f224,f208])).
% 0.21/0.50  fof(f224,plain,(
% 0.21/0.50    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3) | ~m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_9 | ~spl5_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f223,f109])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3) | ~m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f219,f104])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3) | ~m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_18)),
% 0.21/0.50    inference(resolution,[],[f216,f146])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ( ! [X12,X13,X11] : (~r2_hidden(X11,k3_orders_2(sK0,X13,X12)) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X11,X13) | ~m1_subset_1(X11,u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f84,f66])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X12,X13,X11] : (~l1_orders_2(sK0) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X11,X13) | ~r2_hidden(X11,k3_orders_2(sK0,X13,X12))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f83,f46])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X12,X13,X11] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X11,X13) | ~r2_hidden(X11,k3_orders_2(sK0,X13,X12))) ) | (~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f82,f56])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X12,X13,X11] : (~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X11,X13) | ~r2_hidden(X11,k3_orders_2(sK0,X13,X12))) ) | (~spl5_2 | ~spl5_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f72,f51])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X12,X13,X11] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X11,X13) | ~r2_hidden(X11,k3_orders_2(sK0,X13,X12))) ) | ~spl5_4),
% 0.21/0.50    inference(resolution,[],[f61,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    spl5_18 | spl5_10 | ~spl5_11 | ~spl5_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f204,f140,f128,f115,f214])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,sK3,sK1)) | (spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.21/0.50    inference(subsumption_resolution,[],[f203,f130])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,sK3,sK1)) | ~m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_10 | ~spl5_12)),
% 0.21/0.50    inference(resolution,[],[f149,f117])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    ( ! [X2] : (r1_tarski(k3_orders_2(sK0,sK3,sK1),X2) | r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),X2),k3_orders_2(sK0,sK3,sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_12),
% 0.21/0.50    inference(resolution,[],[f142,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK4(X0,X1,X2),X1) | r1_tarski(X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    spl5_17 | spl5_10 | ~spl5_11 | ~spl5_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f198,f140,f128,f115,f206])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0)) | (spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.21/0.50    inference(subsumption_resolution,[],[f197,f130])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0)) | ~m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_10 | ~spl5_12)),
% 0.21/0.50    inference(resolution,[],[f148,f117])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(k3_orders_2(sK0,sK3,sK1),X1) | m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1),X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_12),
% 0.21/0.50    inference(resolution,[],[f142,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK4(X0,X1,X2),X0) | r1_tarski(X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    spl5_12 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f124,f107,f102,f64,f59,f54,f49,f44,f140])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_9)),
% 0.21/0.50    inference(resolution,[],[f122,f104])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,sK3,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_9)),
% 0.21/0.50    inference(resolution,[],[f121,f109])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f76,f66])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f75,f46])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f74,f56])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_2 | ~spl5_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f68,f51])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_4),
% 0.21/0.50    inference(resolution,[],[f61,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl5_11 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f123,f107,f97,f64,f59,f54,f49,f44,f128])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_9)),
% 0.21/0.50    inference(resolution,[],[f122,f99])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ~spl5_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f115])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ~r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) & r2_orders_2(X0,X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) & r2_orders_2(X0,X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_orders_2(X0,X1,X2) => r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f6])).
% 0.21/0.50  fof(f6,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_orders_2(X0,X1,X2) => r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_orders_2)).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl5_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f19,f107])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl5_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f102])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f97])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    spl5_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f20,f92])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    r2_orders_2(sK0,sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f64])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    l1_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f59])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    v5_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f26,f54])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    v4_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f25,f49])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    v3_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ~spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f44])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (1818)------------------------------
% 0.21/0.50  % (1818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1818)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (1818)Memory used [KB]: 10874
% 0.21/0.50  % (1818)Time elapsed: 0.081 s
% 0.21/0.50  % (1818)------------------------------
% 0.21/0.50  % (1818)------------------------------
% 0.21/0.50  % (1811)Success in time 0.138 s
%------------------------------------------------------------------------------
