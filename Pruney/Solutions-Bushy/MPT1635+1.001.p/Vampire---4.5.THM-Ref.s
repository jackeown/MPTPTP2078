%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1635+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:12 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 329 expanded)
%              Number of leaves         :   16 ( 111 expanded)
%              Depth                    :   22
%              Number of atoms          :  620 (1392 expanded)
%              Number of equality atoms :   38 ( 107 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f576,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f70,f76,f82,f442,f466,f478,f498,f528,f543,f562,f575])).

fof(f575,plain,
    ( spl8_4
    | ~ spl8_17
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f574])).

fof(f574,plain,
    ( $false
    | spl8_4
    | ~ spl8_17
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f573,f75])).

fof(f75,plain,
    ( k4_waybel_0(sK0,sK1) != a_2_1_waybel_0(sK0,sK1)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl8_4
  <=> k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f573,plain,
    ( k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,sK1)
    | ~ spl8_17
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f572,f438])).

fof(f438,plain,
    ( r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl8_17
  <=> r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f572,plain,
    ( ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1))
    | k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,sK1)
    | ~ spl8_20 ),
    inference(resolution,[],[f496,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | ~ r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f496,plain,
    ( r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),a_2_1_waybel_0(sK0,sK1))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f495])).

fof(f495,plain,
    ( spl8_20
  <=> r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),a_2_1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f562,plain,
    ( ~ spl8_5
    | ~ spl8_17
    | spl8_21 ),
    inference(avatar_contradiction_clause,[],[f561])).

fof(f561,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_17
    | spl8_21 ),
    inference(subsumption_resolution,[],[f549,f438])).

fof(f549,plain,
    ( ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1))
    | ~ spl8_5
    | spl8_21 ),
    inference(resolution,[],[f542,f86])).

fof(f86,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k4_waybel_0(sK0,sK1)) )
    | ~ spl8_5 ),
    inference(resolution,[],[f81,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f81,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl8_5
  <=> m1_subset_1(k4_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f542,plain,
    ( ~ m1_subset_1(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | spl8_21 ),
    inference(avatar_component_clause,[],[f540])).

fof(f540,plain,
    ( spl8_21
  <=> m1_subset_1(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f543,plain,
    ( spl8_18
    | ~ spl8_21
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_20 ),
    inference(avatar_split_clause,[],[f519,f495,f67,f50,f45,f540,f440])).

fof(f440,plain,
    ( spl8_18
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ r1_orders_2(sK0,X3,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f45,plain,
    ( spl8_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f50,plain,
    ( spl8_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f67,plain,
    ( spl8_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f519,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)))
        | ~ r2_hidden(X0,sK1) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_20 ),
    inference(subsumption_resolution,[],[f513,f69])).

fof(f69,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f513,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl8_1
    | ~ spl8_2
    | spl8_20 ),
    inference(resolution,[],[f497,f59])).

fof(f59,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X1,a_2_1_waybel_0(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f58,f40])).

fof(f58,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ r2_hidden(X2,X0)
        | r2_hidden(X1,a_2_1_waybel_0(sK0,X0)) )
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f54,f52])).

fof(f52,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f54,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ r2_hidden(X2,X0)
        | r2_hidden(X1,a_2_1_waybel_0(sK0,X0)) )
    | spl8_1 ),
    inference(resolution,[],[f47,f43])).

fof(f43,plain,(
    ! [X4,X2,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X4,X3)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X3,a_2_1_waybel_0(X1,X2)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X4,X3)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_waybel_0)).

fof(f47,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f497,plain,
    ( ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),a_2_1_waybel_0(sK0,sK1))
    | spl8_20 ),
    inference(avatar_component_clause,[],[f495])).

fof(f528,plain,
    ( spl8_17
    | spl8_4
    | spl8_20 ),
    inference(avatar_split_clause,[],[f518,f495,f73,f436])).

fof(f518,plain,
    ( r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1))
    | spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f514,f75])).

fof(f514,plain,
    ( r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1))
    | k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,sK1)
    | spl8_20 ),
    inference(resolution,[],[f497,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f498,plain,
    ( ~ spl8_20
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f489,f440,f67,f50,f45,f495])).

fof(f489,plain,
    ( ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),a_2_1_waybel_0(sK0,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f488,f69])).

fof(f488,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),a_2_1_waybel_0(sK0,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_18 ),
    inference(duplicate_literal_removal,[],[f487])).

fof(f487,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),a_2_1_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),a_2_1_waybel_0(sK0,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_18 ),
    inference(resolution,[],[f452,f61])).

fof(f61,plain,
    ( ! [X6,X5] :
        ( r2_hidden(sK7(X6,sK0,X5),X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X6,a_2_1_waybel_0(sK0,X5)) )
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f56,f52])).

fof(f56,plain,
    ( ! [X6,X5] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK7(X6,sK0,X5),X5)
        | ~ r2_hidden(X6,a_2_1_waybel_0(sK0,X5)) )
    | spl8_1 ),
    inference(resolution,[],[f47,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK7(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f452,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),a_2_1_waybel_0(sK0,X0)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_18 ),
    inference(resolution,[],[f441,f101])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,sK7(X0,sK0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,X1)) )
    | spl8_1
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,sK7(X0,sK0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,X1)) )
    | spl8_1
    | ~ spl8_2 ),
    inference(superposition,[],[f60,f62])).

fof(f62,plain,
    ( ! [X8,X7] :
        ( sK6(X8,sK0,X7) = X8
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X8,a_2_1_waybel_0(sK0,X7)) )
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f57,f52])).

fof(f57,plain,
    ( ! [X8,X7] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK6(X8,sK0,X7) = X8
        | ~ r2_hidden(X8,a_2_1_waybel_0(sK0,X7)) )
    | spl8_1 ),
    inference(resolution,[],[f47,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sK6(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f60,plain,
    ( ! [X4,X3] :
        ( r1_orders_2(sK0,sK7(X4,sK0,X3),sK6(X4,sK0,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X4,a_2_1_waybel_0(sK0,X3)) )
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f55,f52])).

fof(f55,plain,
    ( ! [X4,X3] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_orders_2(sK0,sK7(X4,sK0,X3),sK6(X4,sK0,X3))
        | ~ r2_hidden(X4,a_2_1_waybel_0(sK0,X3)) )
    | spl8_1 ),
    inference(resolution,[],[f47,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_orders_2(X1,sK7(X0,X1,X2),sK6(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f441,plain,
    ( ! [X3] :
        ( ~ r1_orders_2(sK0,X3,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f440])).

fof(f478,plain,
    ( ~ spl8_17
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | spl8_19 ),
    inference(avatar_split_clause,[],[f472,f463,f79,f67,f50,f436])).

fof(f463,plain,
    ( spl8_19
  <=> sP3(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f472,plain,
    ( ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1))
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | spl8_19 ),
    inference(subsumption_resolution,[],[f470,f86])).

fof(f470,plain,
    ( ~ m1_subset_1(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1))
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | spl8_19 ),
    inference(resolution,[],[f465,f90])).

fof(f90,plain,
    ( ! [X1] :
        ( sP3(X1,sK1,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k4_waybel_0(sK0,sK1)) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f89,f52])).

fof(f89,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP3(X1,sK1,sK0)
        | ~ r2_hidden(X1,k4_waybel_0(sK0,sK1)) )
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f84,f69])).

fof(f84,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP3(X1,sK1,sK0)
        | ~ r2_hidden(X1,k4_waybel_0(sK0,sK1)) )
    | ~ spl8_5 ),
    inference(resolution,[],[f81,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP3(X3,X1,X0)
      | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_waybel_0)).

fof(f465,plain,
    ( ~ sP3(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),sK1,sK0)
    | spl8_19 ),
    inference(avatar_component_clause,[],[f463])).

fof(f466,plain,
    ( ~ spl8_19
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f457,f440,f463])).

fof(f457,plain,
    ( ~ sP3(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),sK1,sK0)
    | ~ spl8_18 ),
    inference(duplicate_literal_removal,[],[f456])).

fof(f456,plain,
    ( ~ sP3(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),sK1,sK0)
    | ~ sP3(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),sK1,sK0)
    | ~ spl8_18 ),
    inference(resolution,[],[f453,f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X1)
      | ~ sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f453,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(sK0,X1,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1))),sK1)
        | ~ sP3(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),X1,sK0) )
    | ~ spl8_18 ),
    inference(resolution,[],[f441,f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( r1_orders_2(X0,sK4(X0,X1,X3),X3)
      | ~ sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f442,plain,
    ( spl8_17
    | spl8_18
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f434,f79,f73,f67,f50,f45,f440,f436])).

fof(f434,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ r1_orders_2(sK0,X3,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)))
        | r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f433,f75])).

fof(f433,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,sK1)
        | ~ r1_orders_2(sK0,X3,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)))
        | r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f431,f69])).

fof(f431,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,sK1)
        | ~ r1_orders_2(sK0,X3,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)))
        | r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(duplicate_literal_removal,[],[f430])).

fof(f430,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,sK1)
        | ~ r1_orders_2(sK0,X3,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)))
        | r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1))
        | k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,sK1) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(resolution,[],[f339,f32])).

fof(f339,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X1)),a_2_1_waybel_0(sK0,sK1))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,X1)
        | ~ r1_orders_2(sK0,X0,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X1))) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f338,f69])).

fof(f338,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X1)))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X1)),a_2_1_waybel_0(sK0,sK1)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(duplicate_literal_removal,[],[f337])).

fof(f337,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X1)))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X1)),a_2_1_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X1)),a_2_1_waybel_0(sK0,sK1)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(resolution,[],[f229,f61])).

fof(f229,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK7(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X0)),sK0,X1),sK1)
        | ~ r1_orders_2(sK0,X2,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X0)))
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X0)),a_2_1_waybel_0(sK0,X1)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f228,f71])).

fof(f71,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_3 ),
    inference(resolution,[],[f69,f40])).

fof(f228,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK7(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X0)),sK0,X1),sK1)
        | ~ m1_subset_1(sK7(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X0)),sK0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X0)))
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X0)),a_2_1_waybel_0(sK0,X1)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f226,f94])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,X1)) )
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f93,f47])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,X1)) )
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f92,f52])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,X1)) )
    | spl8_1
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,X1)) )
    | spl8_1
    | ~ spl8_2 ),
    inference(superposition,[],[f38,f62])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f226,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X0)),u1_struct_0(sK0))
        | ~ r2_hidden(sK7(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X0)),sK0,X1),sK1)
        | ~ m1_subset_1(sK7(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X0)),sK0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X0)))
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X0)),a_2_1_waybel_0(sK0,X1)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(resolution,[],[f159,f101])).

fof(f159,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_orders_2(sK0,X5,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X4)))
        | ~ m1_subset_1(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X4)),u1_struct_0(sK0))
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X6,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X4)))
        | ~ r2_hidden(X6,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,X4) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X4)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X4)))
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X6,sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X4)))
        | ~ r2_hidden(X6,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK5(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,X4)),u1_struct_0(sK0))
        | k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,X4) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(resolution,[],[f129,f102])).

fof(f102,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK5(X0,a_2_1_waybel_0(sK0,X1)),X0)
        | ~ r1_orders_2(sK0,X2,sK5(X0,a_2_1_waybel_0(sK0,X1)))
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK5(X0,a_2_1_waybel_0(sK0,X1)),u1_struct_0(sK0))
        | a_2_1_waybel_0(sK0,X1) = X0 )
    | spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f59,f33])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(resolution,[],[f88,f22])).

fof(f22,plain,(
    ! [X4,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r1_orders_2(X0,X4,X3)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ sP3(X0,sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k4_waybel_0(sK0,sK1)) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f87,f52])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP3(X0,sK1,sK0)
        | r2_hidden(X0,k4_waybel_0(sK0,sK1)) )
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f83,f69])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP3(X0,sK1,sK0)
        | r2_hidden(X0,k4_waybel_0(sK0,sK1)) )
    | ~ spl8_5 ),
    inference(resolution,[],[f81,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP3(X3,X1,X0)
      | r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k4_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f82,plain,
    ( spl8_5
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f77,f67,f50,f79])).

fof(f77,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f63,f69])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k4_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_2 ),
    inference(resolution,[],[f52,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_0)).

fof(f76,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f19,f73])).

fof(f19,plain,(
    k4_waybel_0(sK0,sK1) != a_2_1_waybel_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_waybel_0(X0,X1) != a_2_1_waybel_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_waybel_0(X0,X1) != a_2_1_waybel_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_waybel_0)).

fof(f70,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f18,f67])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
