%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t26_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:51 EDT 2019

% Result     : Theorem 6.69s
% Output     : Refutation 6.69s
% Verified   : 
% Statistics : Number of formulae       :  110 (1177 expanded)
%              Number of leaves         :   20 ( 278 expanded)
%              Depth                    :   12
%              Number of atoms          :  432 (9778 expanded)
%              Number of equality atoms :   13 ( 170 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9154,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f156,f163,f170,f187,f205,f214,f231,f248,f272,f300,f8929,f9153])).

fof(f9153,plain,
    ( ~ spl11_0
    | spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(avatar_contradiction_clause,[],[f9146])).

fof(f9146,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f117,f186,f9088,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t26_yellow19.p',d3_tarski)).

fof(f9088,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(forward_demodulation,[],[f9068,f8935])).

fof(f8935,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl11_0 ),
    inference(unit_resulting_resolution,[],[f77,f74,f146,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t26_yellow19.p',t52_pre_topc)).

fof(f146,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl11_0
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f74,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,k10_yellow_6(X0,X2))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v3_yellow_6(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,k10_yellow_6(X0,X2))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v3_yellow_6(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( ( l1_waybel_0(X2,X0)
                    & v3_yellow_6(X2,X0)
                    & v7_waybel_0(X2)
                    & v4_orders_2(X2)
                    & ~ v2_struct_0(X2) )
                 => ( r1_waybel_0(X0,X2,X1)
                   => ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r2_hidden(X3,k10_yellow_6(X0,X2))
                         => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v3_yellow_6(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( r1_waybel_0(X0,X2,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,k10_yellow_6(X0,X2))
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t26_yellow19.p',t26_yellow19)).

fof(f77,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f9068,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK0,sK1))
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f77,f169,f76,f162,f155,f75,f213,f204,f247,f230,f74,f271,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_waybel_0(X3)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X0)
      | ~ v3_yellow_6(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | ~ r1_waybel_0(X0,X3,X1)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X3))
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t26_yellow19.p',t24_yellow19)).

fof(f271,plain,
    ( r2_hidden(sK3,k10_yellow_6(sK0,sK2))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl11_18
  <=> r2_hidden(sK3,k10_yellow_6(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f230,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl11_14
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f247,plain,
    ( r1_waybel_0(sK0,sK2,sK1)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl11_16
  <=> r1_waybel_0(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f204,plain,
    ( v3_yellow_6(sK2,sK0)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl11_10
  <=> v3_yellow_6(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f213,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl11_12
  <=> l1_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f75,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f155,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl11_3
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f162,plain,
    ( v4_orders_2(sK2)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl11_4
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f76,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f169,plain,
    ( v7_waybel_0(sK2)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl11_6
  <=> v7_waybel_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f186,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl11_9
  <=> ~ r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f117,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t26_yellow19.p',d10_xboole_0)).

fof(f8929,plain,
    ( spl11_1
    | ~ spl11_24 ),
    inference(avatar_contradiction_clause,[],[f8905])).

fof(f8905,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_24 ),
    inference(unit_resulting_resolution,[],[f196,f401,f415,f416,f414,f417,f418,f419,f420,f299])).

fof(f299,plain,
    ( ! [X2,X3] :
        ( ~ r1_waybel_0(sK0,X2,sK1)
        | r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,k10_yellow_6(sK0,X2))
        | v2_struct_0(X2)
        | ~ l1_waybel_0(X2,sK0)
        | ~ v3_yellow_6(X2,sK0)
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2) )
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl11_24
  <=> ! [X3,X2] :
        ( v2_struct_0(X2)
        | r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,k10_yellow_6(sK0,X2))
        | ~ r1_waybel_0(sK0,X2,sK1)
        | ~ l1_waybel_0(X2,sK0)
        | ~ v3_yellow_6(X2,sK0)
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f420,plain,
    ( r2_hidden(sK10(k2_pre_topc(sK0,sK1),sK1),k10_yellow_6(sK0,sK4(sK0,sK1,sK10(k2_pre_topc(sK0,sK1),sK1))))
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f74,f195,f401,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f195,plain,
    ( r2_hidden(sK10(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1))
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f191,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK10(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f191,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f172,f175,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f175,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f77,f74,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t26_yellow19.p',t48_pre_topc)).

fof(f172,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f76,f77,f149,f74,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f149,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl11_1
  <=> ~ v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f419,plain,
    ( r1_waybel_0(sK0,sK4(sK0,sK1,sK10(k2_pre_topc(sK0,sK1),sK1)),sK1)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f74,f195,f401,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_waybel_0(X0,sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f418,plain,
    ( l1_waybel_0(sK4(sK0,sK1,sK10(k2_pre_topc(sK0,sK1),sK1)),sK0)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f74,f195,f401,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | l1_waybel_0(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f417,plain,
    ( v3_yellow_6(sK4(sK0,sK1,sK10(k2_pre_topc(sK0,sK1),sK1)),sK0)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f74,f195,f401,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v3_yellow_6(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f414,plain,
    ( ~ v2_struct_0(sK4(sK0,sK1,sK10(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f77,f75,f76,f74,f195,f401,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK4(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f416,plain,
    ( v7_waybel_0(sK4(sK0,sK1,sK10(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f74,f195,f401,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v7_waybel_0(sK4(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f415,plain,
    ( v4_orders_2(sK4(sK0,sK1,sK10(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f77,f75,f76,f74,f195,f401,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK4(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f401,plain,
    ( m1_subset_1(sK10(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f173,f195,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t26_yellow19.p',t4_subset)).

fof(f173,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f77,f74,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t26_yellow19.p',dt_k2_pre_topc)).

fof(f196,plain,
    ( ~ r2_hidden(sK10(k2_pre_topc(sK0,sK1),sK1),sK1)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f191,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f300,plain,
    ( spl11_0
    | spl11_24 ),
    inference(avatar_split_clause,[],[f64,f298,f145])).

fof(f64,plain,(
    ! [X2,X3] :
      ( v2_struct_0(X2)
      | ~ v4_orders_2(X2)
      | ~ v7_waybel_0(X2)
      | ~ v3_yellow_6(X2,sK0)
      | ~ l1_waybel_0(X2,sK0)
      | ~ r1_waybel_0(sK0,X2,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,k10_yellow_6(sK0,X2))
      | r2_hidden(X3,sK1)
      | v4_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f272,plain,
    ( ~ spl11_1
    | spl11_18 ),
    inference(avatar_split_clause,[],[f66,f270,f148])).

fof(f66,plain,
    ( r2_hidden(sK3,k10_yellow_6(sK0,sK2))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f248,plain,
    ( ~ spl11_1
    | spl11_16 ),
    inference(avatar_split_clause,[],[f73,f246,f148])).

fof(f73,plain,
    ( r1_waybel_0(sK0,sK2,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f231,plain,
    ( ~ spl11_1
    | spl11_14 ),
    inference(avatar_split_clause,[],[f65,f229,f148])).

fof(f65,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f214,plain,
    ( ~ spl11_1
    | spl11_12 ),
    inference(avatar_split_clause,[],[f72,f212,f148])).

fof(f72,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f205,plain,
    ( ~ spl11_1
    | spl11_10 ),
    inference(avatar_split_clause,[],[f71,f203,f148])).

fof(f71,plain,
    ( v3_yellow_6(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f187,plain,
    ( ~ spl11_1
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f67,f185,f148])).

fof(f67,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f170,plain,
    ( ~ spl11_1
    | spl11_6 ),
    inference(avatar_split_clause,[],[f70,f168,f148])).

fof(f70,plain,
    ( v7_waybel_0(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f163,plain,
    ( ~ spl11_1
    | spl11_4 ),
    inference(avatar_split_clause,[],[f69,f161,f148])).

fof(f69,plain,
    ( v4_orders_2(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f156,plain,
    ( ~ spl11_1
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f68,f154,f148])).

fof(f68,plain,
    ( ~ v2_struct_0(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
