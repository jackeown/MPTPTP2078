%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1944+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:56 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 316 expanded)
%              Number of leaves         :   40 ( 154 expanded)
%              Depth                    :   12
%              Number of atoms          :  940 (2048 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f84,f88,f92,f96,f100,f104,f108,f112,f123,f133,f136,f141,f146,f152,f158,f170,f172,f178,f199,f204,f206,f222,f234])).

fof(f234,plain,
    ( ~ spl7_2
    | ~ spl7_7
    | ~ spl7_8
    | spl7_9
    | ~ spl7_3
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f233,f220,f86,f110,f106,f102,f82])).

fof(f82,plain,
    ( spl7_2
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f102,plain,
    ( spl7_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f106,plain,
    ( spl7_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f110,plain,
    ( spl7_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f86,plain,
    ( spl7_3
  <=> v1_yellow_6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f220,plain,
    ( spl7_28
  <=> ! [X1] :
        ( ~ l1_waybel_0(sK1,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_yellow_6(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f233,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ spl7_3
    | ~ spl7_28 ),
    inference(resolution,[],[f221,f87])).

fof(f87,plain,
    ( v1_yellow_6(sK1,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f221,plain,
    ( ! [X1] :
        ( ~ v1_yellow_6(sK1,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ l1_waybel_0(sK1,X1) )
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f220])).

fof(f222,plain,
    ( spl7_6
    | ~ spl7_5
    | ~ spl7_4
    | spl7_28
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f208,f176,f220,f90,f94,f98])).

fof(f98,plain,
    ( spl7_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f94,plain,
    ( spl7_5
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f90,plain,
    ( spl7_4
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f176,plain,
    ( spl7_20
  <=> ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f208,plain,
    ( ! [X1] :
        ( ~ l1_waybel_0(sK1,X1)
        | ~ v1_yellow_6(sK1,X1)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_20 ),
    inference(resolution,[],[f177,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_6_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_6_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_6_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v1_yellow_6(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(o_2_6_yellow_6(X0,X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_2_6_yellow_6)).

fof(f177,plain,
    ( ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f176])).

fof(f206,plain,
    ( spl7_1
    | ~ spl7_19
    | ~ spl7_17
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f205,f202,f161,f168,f78])).

fof(f78,plain,
    ( spl7_1
  <=> r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f168,plain,
    ( spl7_19
  <=> m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f161,plain,
    ( spl7_17
  <=> r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f202,plain,
    ( spl7_25
  <=> ! [X0] :
        ( ~ r1_waybel_0(sK0,sK1,sK6(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f205,plain,
    ( ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    | ~ spl7_17
    | ~ spl7_25 ),
    inference(resolution,[],[f203,f162])).

fof(f162,plain,
    ( r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f161])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ r1_waybel_0(sK0,sK1,sK6(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) )
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f202])).

fof(f204,plain,
    ( ~ spl7_2
    | spl7_25
    | ~ spl7_8
    | spl7_9
    | ~ spl7_7
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f200,f197,f102,f110,f106,f202,f82])).

fof(f197,plain,
    ( spl7_24
  <=> ! [X1,X0] :
        ( ~ r1_waybel_0(X0,sK1,sK6(X0,sK1,X1))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | r2_hidden(X1,k10_yellow_6(X0,sK1))
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f200,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r1_waybel_0(sK0,sK1,sK6(sK0,sK1,X0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_7
    | ~ spl7_24 ),
    inference(resolution,[],[f198,f103])).

fof(f103,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ r1_waybel_0(X0,sK1,sK6(X0,sK1,X1))
        | r2_hidden(X1,k10_yellow_6(X0,sK1))
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f197])).

fof(f199,plain,
    ( spl7_6
    | ~ spl7_5
    | spl7_24
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f195,f90,f197,f94,f98])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_0(X0,sK1,sK6(X0,sK1,X1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_waybel_0(sK1,X0)
        | r2_hidden(X1,k10_yellow_6(X0,sK1))
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f115,f91])).

fof(f91,plain,
    ( v7_waybel_0(sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f115,plain,(
    ! [X6,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r1_waybel_0(X0,X1,sK6(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f74,f72])).

% (15232)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f74,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ r1_waybel_0(X0,X1,sK6(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_waybel_0(X0,X1,sK6(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X2))
                        & m1_connsp_2(sK5(X0,X1,X2),X0,sK4(X0,X1,X2)) )
                      | ~ r2_hidden(sK4(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK4(X0,X1,X2)) )
                      | r2_hidden(sK4(X0,X1,X2),X2) )
                    & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK6(X0,X1,X6))
                            & m1_connsp_2(sK6(X0,X1,X6),X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f41,f44,f43,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_waybel_0(X0,X1,X4)
                & m1_connsp_2(X4,X0,X3) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( r1_waybel_0(X0,X1,X5)
                | ~ m1_connsp_2(X5,X0,X3) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( ~ r1_waybel_0(X0,X1,X4)
              & m1_connsp_2(X4,X0,sK4(X0,X1,X2)) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK4(X0,X1,X2)) )
          | r2_hidden(sK4(X0,X1,X2),X2) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,sK4(X0,X1,X2)) )
     => ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X2))
        & m1_connsp_2(sK5(X0,X1,X2),X0,sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK6(X0,X1,X6))
        & m1_connsp_2(sK6(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X5] :
                            ( r1_waybel_0(X0,X1,X5)
                            | ~ m1_connsp_2(X5,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ? [X7] :
                              ( ~ r1_waybel_0(X0,X1,X7)
                              & m1_connsp_2(X7,X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_connsp_2(X4,X0,X3)
                         => r1_waybel_0(X0,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).

fof(f178,plain,
    ( spl7_9
    | ~ spl7_12
    | spl7_6
    | ~ spl7_2
    | spl7_17
    | spl7_20
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f174,f164,f176,f161,f82,f98,f130,f110])).

fof(f130,plain,
    ( spl7_12
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f164,plain,
    ( spl7_18
  <=> ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)),X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_18 ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_18 ),
    inference(resolution,[],[f165,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK2(X0,X1,X2,X3))
                      & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK3(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f37,f36])).

fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK2(X0,X1,X2,X3))
        & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK3(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f165,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)),X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f164])).

fof(f172,plain,
    ( spl7_9
    | ~ spl7_12
    | ~ spl7_2
    | spl7_19 ),
    inference(avatar_split_clause,[],[f171,f168,f82,f130,f110])).

fof(f171,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl7_19 ),
    inference(resolution,[],[f169,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_6)).

fof(f169,plain,
    ( ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | spl7_19 ),
    inference(avatar_component_clause,[],[f168])).

fof(f170,plain,
    ( spl7_17
    | spl7_18
    | spl7_1
    | ~ spl7_19
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f159,f156,f139,f168,f78,f164,f161])).

fof(f139,plain,
    ( spl7_13
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_yellow_6(sK0,sK1),X0)
        | ~ m1_subset_1(sK2(sK0,sK1,X0,X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f156,plain,
    ( spl7_16
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK6(sK0,sK1,X0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
        | r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
        | ~ m1_subset_1(sK2(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1)),X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,k4_yellow_6(sK0,sK1))) )
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(resolution,[],[f157,f140])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_yellow_6(sK0,sK1),X0)
        | ~ m1_subset_1(sK2(sK0,sK1,X0,X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,X0) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f139])).

fof(f157,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK6(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f158,plain,
    ( spl7_9
    | ~ spl7_8
    | ~ spl7_7
    | spl7_16
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f154,f149,f156,f102,f106,f110])).

fof(f149,plain,
    ( spl7_15
  <=> ! [X0] :
        ( m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | r2_hidden(X0,sK6(sK0,sK1,X0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_15 ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | r2_hidden(X0,sK6(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_15 ),
    inference(resolution,[],[f150,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X1,X0,X2)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f62,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f150,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1)) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f149])).

fof(f152,plain,
    ( ~ spl7_2
    | spl7_15
    | ~ spl7_8
    | spl7_9
    | ~ spl7_7
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f147,f144,f102,f110,f106,f149,f82])).

fof(f144,plain,
    ( spl7_14
  <=> ! [X1,X0] :
        ( m1_connsp_2(sK6(X0,sK1,X1),X0,X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | r2_hidden(X1,k10_yellow_6(X0,sK1))
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f147,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_7
    | ~ spl7_14 ),
    inference(resolution,[],[f145,f103])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | m1_connsp_2(sK6(X0,sK1,X1),X0,X1)
        | r2_hidden(X1,k10_yellow_6(X0,sK1))
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f146,plain,
    ( spl7_6
    | ~ spl7_5
    | spl7_14
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f142,f90,f144,f94,f98])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( m1_connsp_2(sK6(X0,sK1,X1),X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_waybel_0(sK1,X0)
        | r2_hidden(X1,k10_yellow_6(X0,sK1))
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f114,f91])).

fof(f114,plain,(
    ! [X6,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | m1_connsp_2(sK6(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f75,f72])).

fof(f75,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | m1_connsp_2(sK6(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_connsp_2(sK6(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f141,plain,
    ( spl7_9
    | ~ spl7_12
    | spl7_6
    | ~ spl7_2
    | spl7_13
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f137,f126,f139,f82,f98,f130,f110])).

fof(f126,plain,
    ( spl7_11
  <=> ! [X0] :
        ( k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_yellow_6(sK0,sK1),X0)
        | r1_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(sK2(sK0,sK1,X0,X1),u1_struct_0(sK1)) )
    | ~ spl7_11 ),
    inference(superposition,[],[f61,f127])).

fof(f127,plain,
    ( ! [X0] :
        ( k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f136,plain,
    ( ~ spl7_7
    | spl7_12 ),
    inference(avatar_split_clause,[],[f134,f130,f102])).

fof(f134,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_12 ),
    inference(resolution,[],[f131,f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f131,plain,
    ( ~ l1_struct_0(sK0)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f133,plain,
    ( spl7_11
    | ~ spl7_2
    | ~ spl7_12
    | spl7_9
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f124,f121,f86,f110,f130,f82,f126])).

fof(f121,plain,
    ( spl7_10
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(X1)
        | ~ l1_struct_0(X1)
        | ~ l1_waybel_0(sK1,X1)
        | k4_yellow_6(X1,sK1) = k2_waybel_0(X1,sK1,X0)
        | ~ v1_yellow_6(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f124,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ l1_struct_0(sK0)
        | ~ l1_waybel_0(sK1,sK0)
        | k4_yellow_6(sK0,sK1) = k2_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(resolution,[],[f122,f87])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ v1_yellow_6(sK1,X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X1)
        | ~ l1_waybel_0(sK1,X1)
        | k4_yellow_6(X1,sK1) = k2_waybel_0(X1,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,
    ( spl7_6
    | ~ spl7_5
    | spl7_10
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f117,f90,f121,f94,f98])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,X1)
        | ~ v1_yellow_6(sK1,X1)
        | k4_yellow_6(X1,sK1) = k2_waybel_0(X1,sK1,X0)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(X1)
        | v2_struct_0(X1) )
    | ~ spl7_4 ),
    inference(resolution,[],[f56,f91])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | k4_yellow_6(X0,X1) = k2_waybel_0(X0,X1,X2)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_yellow_6(X0,X1) = k2_waybel_0(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_yellow_6(X0,X1) = k2_waybel_0(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k4_yellow_6(X0,X1) = k2_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_6)).

fof(f112,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f46,f110])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
    & l1_waybel_0(sK1,sK0)
    & v1_yellow_6(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
            & l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r2_hidden(k4_yellow_6(sK0,X1),k10_yellow_6(sK0,X1))
          & l1_waybel_0(X1,sK0)
          & v1_yellow_6(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ~ r2_hidden(k4_yellow_6(sK0,X1),k10_yellow_6(sK0,X1))
        & l1_waybel_0(X1,sK0)
        & v1_yellow_6(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ~ r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1))
      & l1_waybel_0(sK1,sK0)
      & v1_yellow_6(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v1_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_6)).

fof(f108,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f47,f106])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f48,f102])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f100,plain,(
    ~ spl7_6 ),
    inference(avatar_split_clause,[],[f49,f98])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f96,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f50,f94])).

fof(f50,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f51,f90])).

fof(f51,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f52,f86])).

fof(f52,plain,(
    v1_yellow_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f53,f82])).

fof(f53,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f54,f78])).

fof(f54,plain,(
    ~ r2_hidden(k4_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

%------------------------------------------------------------------------------
