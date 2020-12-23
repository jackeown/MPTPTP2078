%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t40_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:50 EDT 2019

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 529 expanded)
%              Number of leaves         :   32 ( 230 expanded)
%              Depth                    :   15
%              Number of atoms          : 1175 (2469 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f106,f110,f114,f118,f149,f158,f163,f176,f189,f219,f227,f255,f297,f305,f653,f719,f1254,f1258,f1422,f1659,f12040,f12921,f14141,f14426,f15000,f15132])).

fof(f15132,plain,
    ( spl12_244
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_20
    | ~ spl12_24
    | ~ spl12_40 ),
    inference(avatar_split_clause,[],[f15001,f253,f187,f174,f147,f300,f116,f108,f2269])).

fof(f2269,plain,
    ( spl12_244
  <=> r2_hidden(sK7(sK0,sK1,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_244])])).

fof(f108,plain,
    ( spl12_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f116,plain,
    ( spl12_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f300,plain,
    ( spl12_10
  <=> v1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f147,plain,
    ( spl12_12
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f174,plain,
    ( spl12_20
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f187,plain,
    ( spl12_24
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f253,plain,
    ( spl12_40
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_40])])).

fof(f15001,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2,sK3),sK1)
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_20
    | ~ spl12_24
    | ~ spl12_40 ),
    inference(subsumption_resolution,[],[f13554,f175])).

fof(f175,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f174])).

fof(f13554,plain,
    ( ~ r2_hidden(sK3,sK1)
    | r2_hidden(sK7(sK0,sK1,sK2,sK3),sK1)
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_24
    | ~ spl12_40 ),
    inference(resolution,[],[f13049,f188])).

fof(f188,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl12_24 ),
    inference(avatar_component_clause,[],[f187])).

fof(f13049,plain,
    ( ! [X58] :
        ( ~ m1_subset_1(X58,u1_struct_0(sK0))
        | ~ r2_hidden(X58,sK1)
        | r2_hidden(sK7(sK0,sK1,sK2,X58),sK1) )
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_40 ),
    inference(subsumption_resolution,[],[f13011,f148])).

fof(f148,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f13011,plain,
    ( ! [X58] :
        ( ~ m1_subset_1(X58,u1_struct_0(sK0))
        | ~ r2_hidden(sK2,sK1)
        | ~ r2_hidden(X58,sK1)
        | r2_hidden(sK7(sK0,sK1,sK2,X58),sK1) )
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_40 ),
    inference(resolution,[],[f12948,f254])).

fof(f254,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl12_40 ),
    inference(avatar_component_clause,[],[f253])).

fof(f12948,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1)
        | ~ r2_hidden(X3,sK1)
        | r2_hidden(sK7(sK0,sK1,X2,X3),sK1) )
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f134,f301])).

fof(f301,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f300])).

fof(f134,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1)
        | ~ r2_hidden(X3,sK1)
        | r2_hidden(sK7(sK0,sK1,X2,X3),sK1)
        | ~ v1_waybel_0(sK1,sK0) )
    | ~ spl12_4
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f120,f109])).

fof(f109,plain,
    ( l1_orders_2(sK0)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f120,plain,
    ( ! [X2,X3] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1)
        | ~ r2_hidden(X3,sK1)
        | r2_hidden(sK7(sK0,sK1,X2,X3),sK1)
        | ~ v1_waybel_0(sK1,sK0) )
    | ~ spl12_8 ),
    inference(resolution,[],[f117,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(sK7(X0,X1,X2,X3),X1)
      | ~ v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X3,X4)
                                & r1_orders_2(X0,X2,X4)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t40_waybel_0.p',d1_waybel_0)).

fof(f117,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f15000,plain,
    ( spl12_268
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_20
    | ~ spl12_24
    | ~ spl12_40 ),
    inference(avatar_split_clause,[],[f14427,f253,f187,f174,f147,f300,f116,f108,f2711])).

fof(f2711,plain,
    ( spl12_268
  <=> r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_268])])).

fof(f14427,plain,
    ( r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK2,sK3))
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_20
    | ~ spl12_24
    | ~ spl12_40 ),
    inference(subsumption_resolution,[],[f14368,f175])).

fof(f14368,plain,
    ( ~ r2_hidden(sK3,sK1)
    | r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK2,sK3))
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_24
    | ~ spl12_40 ),
    inference(resolution,[],[f13459,f188])).

fof(f13459,plain,
    ( ! [X58] :
        ( ~ m1_subset_1(X58,u1_struct_0(sK0))
        | ~ r2_hidden(X58,sK1)
        | r1_orders_2(sK0,X58,sK7(sK0,sK1,sK2,X58)) )
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_40 ),
    inference(subsumption_resolution,[],[f13422,f148])).

fof(f13422,plain,
    ( ! [X58] :
        ( ~ m1_subset_1(X58,u1_struct_0(sK0))
        | ~ r2_hidden(sK2,sK1)
        | ~ r2_hidden(X58,sK1)
        | r1_orders_2(sK0,X58,sK7(sK0,sK1,sK2,X58)) )
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_40 ),
    inference(resolution,[],[f12950,f254])).

fof(f12950,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(X6,sK1)
        | ~ r2_hidden(X7,sK1)
        | r1_orders_2(sK0,X7,sK7(sK0,sK1,X6,X7)) )
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f136,f301])).

fof(f136,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(X6,sK1)
        | ~ r2_hidden(X7,sK1)
        | r1_orders_2(sK0,X7,sK7(sK0,sK1,X6,X7))
        | ~ v1_waybel_0(sK1,sK0) )
    | ~ spl12_4
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f122,f109])).

fof(f122,plain,
    ( ! [X6,X7] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(X6,sK1)
        | ~ r2_hidden(X7,sK1)
        | r1_orders_2(sK0,X7,sK7(sK0,sK1,X6,X7))
        | ~ v1_waybel_0(sK1,sK0) )
    | ~ spl12_8 ),
    inference(resolution,[],[f117,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
      | ~ v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14426,plain,
    ( spl12_280
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_20
    | ~ spl12_24
    | ~ spl12_40 ),
    inference(avatar_split_clause,[],[f14142,f253,f187,f174,f147,f300,f116,f108,f2738])).

fof(f2738,plain,
    ( spl12_280
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_280])])).

fof(f14142,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_20
    | ~ spl12_24
    | ~ spl12_40 ),
    inference(subsumption_resolution,[],[f13835,f175])).

fof(f13835,plain,
    ( ~ r2_hidden(sK3,sK1)
    | m1_subset_1(sK7(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_24
    | ~ spl12_40 ),
    inference(resolution,[],[f13177,f188])).

fof(f13177,plain,
    ( ! [X58] :
        ( ~ m1_subset_1(X58,u1_struct_0(sK0))
        | ~ r2_hidden(X58,sK1)
        | m1_subset_1(sK7(sK0,sK1,sK2,X58),u1_struct_0(sK0)) )
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_40 ),
    inference(subsumption_resolution,[],[f13140,f148])).

fof(f13140,plain,
    ( ! [X58] :
        ( ~ m1_subset_1(X58,u1_struct_0(sK0))
        | ~ r2_hidden(sK2,sK1)
        | ~ r2_hidden(X58,sK1)
        | m1_subset_1(sK7(sK0,sK1,sK2,X58),u1_struct_0(sK0)) )
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_40 ),
    inference(resolution,[],[f12947,f254])).

fof(f12947,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1)
        | m1_subset_1(sK7(sK0,sK1,X0,X1),u1_struct_0(sK0)) )
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f133,f301])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1)
        | m1_subset_1(sK7(sK0,sK1,X0,X1),u1_struct_0(sK0))
        | ~ v1_waybel_0(sK1,sK0) )
    | ~ spl12_4
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f119,f109])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1)
        | m1_subset_1(sK7(sK0,sK1,X0,X1),u1_struct_0(sK0))
        | ~ v1_waybel_0(sK1,sK0) )
    | ~ spl12_8 ),
    inference(resolution,[],[f117,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X3,X1)
      | m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14141,plain,
    ( spl12_274
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_20
    | ~ spl12_24
    | ~ spl12_40 ),
    inference(avatar_split_clause,[],[f14112,f253,f187,f174,f147,f300,f116,f108,f2725])).

fof(f2725,plain,
    ( spl12_274
  <=> r1_orders_2(sK0,sK2,sK7(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_274])])).

fof(f14112,plain,
    ( r1_orders_2(sK0,sK2,sK7(sK0,sK1,sK2,sK3))
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_20
    | ~ spl12_24
    | ~ spl12_40 ),
    inference(subsumption_resolution,[],[f14079,f175])).

fof(f14079,plain,
    ( ~ r2_hidden(sK3,sK1)
    | r1_orders_2(sK0,sK2,sK7(sK0,sK1,sK2,sK3))
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_24
    | ~ spl12_40 ),
    inference(resolution,[],[f13328,f188])).

fof(f13328,plain,
    ( ! [X58] :
        ( ~ m1_subset_1(X58,u1_struct_0(sK0))
        | ~ r2_hidden(X58,sK1)
        | r1_orders_2(sK0,sK2,sK7(sK0,sK1,sK2,X58)) )
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_40 ),
    inference(subsumption_resolution,[],[f13291,f148])).

fof(f13291,plain,
    ( ! [X58] :
        ( ~ m1_subset_1(X58,u1_struct_0(sK0))
        | ~ r2_hidden(sK2,sK1)
        | ~ r2_hidden(X58,sK1)
        | r1_orders_2(sK0,sK2,sK7(sK0,sK1,sK2,X58)) )
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_40 ),
    inference(resolution,[],[f12949,f254])).

fof(f12949,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK1)
        | r1_orders_2(sK0,X4,sK7(sK0,sK1,X4,X5)) )
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f135,f301])).

fof(f135,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK1)
        | r1_orders_2(sK0,X4,sK7(sK0,sK1,X4,X5))
        | ~ v1_waybel_0(sK1,sK0) )
    | ~ spl12_4
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f121,f109])).

fof(f121,plain,
    ( ! [X4,X5] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK1)
        | r1_orders_2(sK0,X4,sK7(sK0,sK1,X4,X5))
        | ~ v1_waybel_0(sK1,sK0) )
    | ~ spl12_8 ),
    inference(resolution,[],[f117,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
      | ~ v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12921,plain,
    ( ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | spl12_47
    | ~ spl12_208
    | ~ spl12_244
    | ~ spl12_280
    | ~ spl12_910 ),
    inference(avatar_contradiction_clause,[],[f12920])).

fof(f12920,plain,
    ( $false
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_47
    | ~ spl12_208
    | ~ spl12_244
    | ~ spl12_280
    | ~ spl12_910 ),
    inference(subsumption_resolution,[],[f12919,f296])).

fof(f296,plain,
    ( ~ r2_hidden(k13_lattice3(sK0,sK2,sK3),sK1)
    | ~ spl12_47 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl12_47
  <=> ~ r2_hidden(k13_lattice3(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_47])])).

fof(f12919,plain,
    ( r2_hidden(k13_lattice3(sK0,sK2,sK3),sK1)
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_208
    | ~ spl12_244
    | ~ spl12_280
    | ~ spl12_910 ),
    inference(subsumption_resolution,[],[f12918,f2739])).

fof(f2739,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ spl12_280 ),
    inference(avatar_component_clause,[],[f2738])).

fof(f12918,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | r2_hidden(k13_lattice3(sK0,sK2,sK3),sK1)
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_208
    | ~ spl12_244
    | ~ spl12_910 ),
    inference(subsumption_resolution,[],[f12917,f2270])).

fof(f2270,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2,sK3),sK1)
    | ~ spl12_244 ),
    inference(avatar_component_clause,[],[f2269])).

fof(f12917,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK2,sK3),sK1)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | r2_hidden(k13_lattice3(sK0,sK2,sK3),sK1)
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_208
    | ~ spl12_910 ),
    inference(subsumption_resolution,[],[f12913,f1658])).

fof(f1658,plain,
    ( m1_subset_1(k13_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl12_208 ),
    inference(avatar_component_clause,[],[f1657])).

fof(f1657,plain,
    ( spl12_208
  <=> m1_subset_1(k13_lattice3(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_208])])).

fof(f12913,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK7(sK0,sK1,sK2,sK3),sK1)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | r2_hidden(k13_lattice3(sK0,sK2,sK3),sK1)
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_910 ),
    inference(resolution,[],[f12039,f142])).

fof(f142,plain,
    ( ! [X8,X9] :
        ( ~ r1_orders_2(sK0,X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ r2_hidden(X8,sK1)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r2_hidden(X9,sK1) )
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f141,f113])).

fof(f113,plain,
    ( v12_waybel_0(sK1,sK0)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl12_6
  <=> v12_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f141,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ r2_hidden(X8,sK1)
        | ~ r1_orders_2(sK0,X9,X8)
        | r2_hidden(X9,sK1)
        | ~ v12_waybel_0(sK1,sK0) )
    | ~ spl12_4
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f130,f109])).

fof(f130,plain,
    ( ! [X8,X9] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ r2_hidden(X8,sK1)
        | ~ r1_orders_2(sK0,X9,X8)
        | r2_hidden(X9,sK1)
        | ~ v12_waybel_0(sK1,sK0) )
    | ~ spl12_8 ),
    inference(resolution,[],[f117,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | r2_hidden(X3,X1)
      | ~ v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X3,X2)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t40_waybel_0.p',d19_waybel_0)).

fof(f12039,plain,
    ( r1_orders_2(sK0,k13_lattice3(sK0,sK2,sK3),sK7(sK0,sK1,sK2,sK3))
    | ~ spl12_910 ),
    inference(avatar_component_clause,[],[f12038])).

fof(f12038,plain,
    ( spl12_910
  <=> r1_orders_2(sK0,k13_lattice3(sK0,sK2,sK3),sK7(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_910])])).

fof(f12040,plain,
    ( spl12_910
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_24
    | ~ spl12_40
    | ~ spl12_208
    | ~ spl12_268
    | ~ spl12_274
    | ~ spl12_280 ),
    inference(avatar_split_clause,[],[f11473,f2738,f2725,f2711,f1657,f253,f187,f108,f104,f100,f12038])).

fof(f100,plain,
    ( spl12_0
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f104,plain,
    ( spl12_2
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f11473,plain,
    ( r1_orders_2(sK0,k13_lattice3(sK0,sK2,sK3),sK7(sK0,sK1,sK2,sK3))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_24
    | ~ spl12_40
    | ~ spl12_208
    | ~ spl12_268
    | ~ spl12_274
    | ~ spl12_280 ),
    inference(subsumption_resolution,[],[f11472,f2739])).

fof(f11472,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK0,k13_lattice3(sK0,sK2,sK3),sK7(sK0,sK1,sK2,sK3))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_24
    | ~ spl12_40
    | ~ spl12_208
    | ~ spl12_268
    | ~ spl12_274 ),
    inference(subsumption_resolution,[],[f11455,f2726])).

fof(f2726,plain,
    ( r1_orders_2(sK0,sK2,sK7(sK0,sK1,sK2,sK3))
    | ~ spl12_274 ),
    inference(avatar_component_clause,[],[f2725])).

fof(f11455,plain,
    ( ~ r1_orders_2(sK0,sK2,sK7(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK0,k13_lattice3(sK0,sK2,sK3),sK7(sK0,sK1,sK2,sK3))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_24
    | ~ spl12_40
    | ~ spl12_208
    | ~ spl12_268 ),
    inference(resolution,[],[f1727,f2712])).

fof(f2712,plain,
    ( r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK2,sK3))
    | ~ spl12_268 ),
    inference(avatar_component_clause,[],[f2711])).

fof(f1727,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK3,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k13_lattice3(sK0,sK2,sK3),X0) )
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_24
    | ~ spl12_40
    | ~ spl12_208 ),
    inference(subsumption_resolution,[],[f1726,f101])).

fof(f101,plain,
    ( v5_orders_2(sK0)
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f100])).

fof(f1726,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK3,X0)
        | r1_orders_2(sK0,k13_lattice3(sK0,sK2,sK3),X0) )
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_24
    | ~ spl12_40
    | ~ spl12_208 ),
    inference(subsumption_resolution,[],[f1725,f188])).

fof(f1725,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK3,X0)
        | r1_orders_2(sK0,k13_lattice3(sK0,sK2,sK3),X0) )
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_40
    | ~ spl12_208 ),
    inference(subsumption_resolution,[],[f1724,f254])).

fof(f1724,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK3,X0)
        | r1_orders_2(sK0,k13_lattice3(sK0,sK2,sK3),X0) )
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_208 ),
    inference(subsumption_resolution,[],[f1723,f109])).

fof(f1723,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK3,X0)
        | r1_orders_2(sK0,k13_lattice3(sK0,sK2,sK3),X0) )
    | ~ spl12_2
    | ~ spl12_208 ),
    inference(subsumption_resolution,[],[f1705,f105])).

fof(f105,plain,
    ( v1_lattice3(sK0)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f1705,plain,
    ( ! [X0] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK3,X0)
        | r1_orders_2(sK0,k13_lattice3(sK0,sK2,sK3),X0) )
    | ~ spl12_208 ),
    inference(resolution,[],[f1658,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X4)
      | ~ r1_orders_2(X0,X2,X4)
      | r1_orders_2(X0,k13_lattice3(X0,X1,X2),X4) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X4)
      | ~ r1_orders_2(X0,X2,X4)
      | r1_orders_2(X0,X3,X4)
      | k13_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t40_waybel_0.p',t22_yellow_0)).

fof(f1659,plain,
    ( spl12_208
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_24
    | ~ spl12_40 ),
    inference(avatar_split_clause,[],[f1472,f253,f187,f108,f104,f100,f1657])).

fof(f1472,plain,
    ( m1_subset_1(k13_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_24
    | ~ spl12_40 ),
    inference(resolution,[],[f1404,f188])).

fof(f1404,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(k13_lattice3(sK0,sK2,X1),u1_struct_0(sK0)) )
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_40 ),
    inference(subsumption_resolution,[],[f1403,f101])).

fof(f1403,plain,
    ( ! [X1] :
        ( ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(k13_lattice3(sK0,sK2,X1),u1_struct_0(sK0)) )
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_40 ),
    inference(subsumption_resolution,[],[f1402,f109])).

fof(f1402,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(k13_lattice3(sK0,sK2,X1),u1_struct_0(sK0)) )
    | ~ spl12_2
    | ~ spl12_40 ),
    inference(subsumption_resolution,[],[f1394,f105])).

fof(f1394,plain,
    ( ! [X1] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(k13_lattice3(sK0,sK2,X1),u1_struct_0(sK0)) )
    | ~ spl12_40 ),
    inference(resolution,[],[f254,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t40_waybel_0.p',dt_k13_lattice3)).

fof(f1422,plain,
    ( spl12_10
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_98
    | ~ spl12_122
    | ~ spl12_178
    | ~ spl12_180 ),
    inference(avatar_split_clause,[],[f1347,f1256,f1252,f717,f651,f116,f108,f300])).

fof(f651,plain,
    ( spl12_98
  <=> r2_hidden(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_98])])).

fof(f717,plain,
    ( spl12_122
  <=> m1_subset_1(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_122])])).

fof(f1252,plain,
    ( spl12_178
  <=> r1_orders_2(sK0,sK5(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_178])])).

fof(f1256,plain,
    ( spl12_180
  <=> r1_orders_2(sK0,sK6(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_180])])).

fof(f1347,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_98
    | ~ spl12_122
    | ~ spl12_178
    | ~ spl12_180 ),
    inference(subsumption_resolution,[],[f1346,f109])).

fof(f1346,plain,
    ( ~ l1_orders_2(sK0)
    | v1_waybel_0(sK1,sK0)
    | ~ spl12_8
    | ~ spl12_98
    | ~ spl12_122
    | ~ spl12_178
    | ~ spl12_180 ),
    inference(subsumption_resolution,[],[f1345,f1253])).

fof(f1253,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ spl12_178 ),
    inference(avatar_component_clause,[],[f1252])).

fof(f1345,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | v1_waybel_0(sK1,sK0)
    | ~ spl12_8
    | ~ spl12_98
    | ~ spl12_122
    | ~ spl12_180 ),
    inference(subsumption_resolution,[],[f1344,f652])).

fof(f652,plain,
    ( r2_hidden(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK1)
    | ~ spl12_98 ),
    inference(avatar_component_clause,[],[f651])).

fof(f1344,plain,
    ( ~ r2_hidden(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK1)
    | ~ r1_orders_2(sK0,sK5(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | v1_waybel_0(sK1,sK0)
    | ~ spl12_8
    | ~ spl12_122
    | ~ spl12_180 ),
    inference(subsumption_resolution,[],[f1343,f718])).

fof(f718,plain,
    ( m1_subset_1(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl12_122 ),
    inference(avatar_component_clause,[],[f717])).

fof(f1343,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_hidden(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK1)
    | ~ r1_orders_2(sK0,sK5(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | v1_waybel_0(sK1,sK0)
    | ~ spl12_8
    | ~ spl12_180 ),
    inference(subsumption_resolution,[],[f1339,f117])).

fof(f1339,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_hidden(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK1)
    | ~ r1_orders_2(sK0,sK5(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | v1_waybel_0(sK1,sK0)
    | ~ spl12_180 ),
    inference(resolution,[],[f1257,f82])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,X1),X4)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_hidden(X4,X1)
      | ~ r1_orders_2(X0,sK5(X0,X1),X4)
      | ~ l1_orders_2(X0)
      | v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1257,plain,
    ( r1_orders_2(sK0,sK6(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ spl12_180 ),
    inference(avatar_component_clause,[],[f1256])).

fof(f1258,plain,
    ( spl12_180
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_32
    | ~ spl12_36
    | ~ spl12_122 ),
    inference(avatar_split_clause,[],[f830,f717,f225,f217,f108,f104,f100,f1256])).

fof(f217,plain,
    ( spl12_32
  <=> m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).

fof(f225,plain,
    ( spl12_36
  <=> m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_36])])).

fof(f830,plain,
    ( r1_orders_2(sK0,sK6(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_32
    | ~ spl12_36
    | ~ spl12_122 ),
    inference(subsumption_resolution,[],[f829,f101])).

fof(f829,plain,
    ( ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK6(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_32
    | ~ spl12_36
    | ~ spl12_122 ),
    inference(subsumption_resolution,[],[f828,f218])).

fof(f218,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl12_32 ),
    inference(avatar_component_clause,[],[f217])).

fof(f828,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK6(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_36
    | ~ spl12_122 ),
    inference(subsumption_resolution,[],[f827,f226])).

fof(f226,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl12_36 ),
    inference(avatar_component_clause,[],[f225])).

fof(f827,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK6(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_122 ),
    inference(subsumption_resolution,[],[f826,f109])).

fof(f826,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK6(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ spl12_2
    | ~ spl12_122 ),
    inference(subsumption_resolution,[],[f805,f105])).

fof(f805,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK6(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ spl12_122 ),
    inference(resolution,[],[f718,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1254,plain,
    ( spl12_178
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_32
    | ~ spl12_36
    | ~ spl12_122 ),
    inference(avatar_split_clause,[],[f825,f717,f225,f217,f108,f104,f100,f1252])).

fof(f825,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_32
    | ~ spl12_36
    | ~ spl12_122 ),
    inference(subsumption_resolution,[],[f824,f101])).

fof(f824,plain,
    ( ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK5(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_32
    | ~ spl12_36
    | ~ spl12_122 ),
    inference(subsumption_resolution,[],[f823,f218])).

fof(f823,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK5(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_36
    | ~ spl12_122 ),
    inference(subsumption_resolution,[],[f822,f226])).

fof(f822,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK5(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_122 ),
    inference(subsumption_resolution,[],[f821,f109])).

fof(f821,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK5(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ spl12_2
    | ~ spl12_122 ),
    inference(subsumption_resolution,[],[f804,f105])).

fof(f804,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK5(sK0,sK1),k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))
    | ~ spl12_122 ),
    inference(resolution,[],[f718,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X3)
      | k13_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f719,plain,
    ( spl12_122
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_32
    | ~ spl12_36 ),
    inference(avatar_split_clause,[],[f611,f225,f217,f108,f104,f100,f717])).

fof(f611,plain,
    ( m1_subset_1(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_32
    | ~ spl12_36 ),
    inference(resolution,[],[f315,f218])).

fof(f315,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(k13_lattice3(sK0,sK5(sK0,sK1),X0),u1_struct_0(sK0)) )
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_36 ),
    inference(subsumption_resolution,[],[f314,f101])).

fof(f314,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(k13_lattice3(sK0,sK5(sK0,sK1),X0),u1_struct_0(sK0)) )
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_36 ),
    inference(subsumption_resolution,[],[f313,f109])).

fof(f313,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(k13_lattice3(sK0,sK5(sK0,sK1),X0),u1_struct_0(sK0)) )
    | ~ spl12_2
    | ~ spl12_36 ),
    inference(subsumption_resolution,[],[f310,f105])).

fof(f310,plain,
    ( ! [X0] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(k13_lattice3(sK0,sK5(sK0,sK1),X0),u1_struct_0(sK0)) )
    | ~ spl12_36 ),
    inference(resolution,[],[f226,f64])).

fof(f653,plain,
    ( spl12_98
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_32
    | ~ spl12_36
    | ~ spl12_48 ),
    inference(avatar_split_clause,[],[f624,f303,f225,f217,f161,f156,f651])).

fof(f156,plain,
    ( spl12_14
  <=> r2_hidden(sK6(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f161,plain,
    ( spl12_16
  <=> r2_hidden(sK5(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f303,plain,
    ( spl12_48
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_hidden(k13_lattice3(sK0,X2,X3),sK1)
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_48])])).

fof(f624,plain,
    ( r2_hidden(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK1)
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_32
    | ~ spl12_36
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f621,f157])).

fof(f157,plain,
    ( r2_hidden(sK6(sK0,sK1),sK1)
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f621,plain,
    ( r2_hidden(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK1)
    | ~ r2_hidden(sK6(sK0,sK1),sK1)
    | ~ spl12_16
    | ~ spl12_32
    | ~ spl12_36
    | ~ spl12_48 ),
    inference(resolution,[],[f341,f218])).

fof(f341,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(k13_lattice3(sK0,sK5(sK0,sK1),X1),sK1)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl12_16
    | ~ spl12_36
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f337,f162])).

fof(f162,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f161])).

fof(f337,plain,
    ( ! [X1] :
        ( r2_hidden(k13_lattice3(sK0,sK5(sK0,sK1),X1),sK1)
        | ~ r2_hidden(sK5(sK0,sK1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl12_36
    | ~ spl12_48 ),
    inference(resolution,[],[f304,f226])).

fof(f304,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_hidden(k13_lattice3(sK0,X2,X3),sK1)
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl12_48 ),
    inference(avatar_component_clause,[],[f303])).

fof(f305,plain,
    ( spl12_10
    | spl12_48 ),
    inference(avatar_split_clause,[],[f52,f303,f300])).

fof(f52,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(k13_lattice3(sK0,X2,X3),sK1)
      | v1_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0) )
           => ( v1_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( ( r2_hidden(X3,X1)
                          & r2_hidden(X2,X1) )
                       => r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t40_waybel_0.p',t40_waybel_0)).

fof(f297,plain,
    ( ~ spl12_11
    | ~ spl12_47 ),
    inference(avatar_split_clause,[],[f56,f295,f144])).

fof(f144,plain,
    ( spl12_11
  <=> ~ v1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f56,plain,
    ( ~ r2_hidden(k13_lattice3(sK0,sK2,sK3),sK1)
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f255,plain,
    ( ~ spl12_11
    | spl12_40 ),
    inference(avatar_split_clause,[],[f57,f253,f144])).

fof(f57,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f227,plain,
    ( spl12_36
    | ~ spl12_4
    | ~ spl12_8
    | spl12_11 ),
    inference(avatar_split_clause,[],[f192,f144,f116,f108,f225])).

fof(f192,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_11 ),
    inference(subsumption_resolution,[],[f140,f145])).

fof(f145,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f144])).

fof(f140,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v1_waybel_0(sK1,sK0)
    | ~ spl12_4
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f126,f109])).

fof(f126,plain,
    ( ~ l1_orders_2(sK0)
    | m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v1_waybel_0(sK1,sK0)
    | ~ spl12_8 ),
    inference(resolution,[],[f117,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f219,plain,
    ( spl12_32
    | ~ spl12_4
    | ~ spl12_8
    | spl12_11 ),
    inference(avatar_split_clause,[],[f191,f144,f116,f108,f217])).

fof(f191,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_11 ),
    inference(subsumption_resolution,[],[f137,f145])).

fof(f137,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | v1_waybel_0(sK1,sK0)
    | ~ spl12_4
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f123,f109])).

fof(f123,plain,
    ( ~ l1_orders_2(sK0)
    | m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | v1_waybel_0(sK1,sK0)
    | ~ spl12_8 ),
    inference(resolution,[],[f117,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f189,plain,
    ( ~ spl12_11
    | spl12_24 ),
    inference(avatar_split_clause,[],[f53,f187,f144])).

fof(f53,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f176,plain,
    ( ~ spl12_11
    | spl12_20 ),
    inference(avatar_split_clause,[],[f55,f174,f144])).

fof(f55,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f163,plain,
    ( spl12_16
    | ~ spl12_4
    | ~ spl12_8
    | spl12_11 ),
    inference(avatar_split_clause,[],[f152,f144,f116,f108,f161])).

fof(f152,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_11 ),
    inference(subsumption_resolution,[],[f138,f145])).

fof(f138,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | v1_waybel_0(sK1,sK0)
    | ~ spl12_4
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f124,f109])).

fof(f124,plain,
    ( ~ l1_orders_2(sK0)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | v1_waybel_0(sK1,sK0)
    | ~ spl12_8 ),
    inference(resolution,[],[f117,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1),X1)
      | v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f158,plain,
    ( spl12_14
    | ~ spl12_4
    | ~ spl12_8
    | spl12_11 ),
    inference(avatar_split_clause,[],[f151,f144,f116,f108,f156])).

fof(f151,plain,
    ( r2_hidden(sK6(sK0,sK1),sK1)
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_11 ),
    inference(subsumption_resolution,[],[f139,f145])).

fof(f139,plain,
    ( r2_hidden(sK6(sK0,sK1),sK1)
    | v1_waybel_0(sK1,sK0)
    | ~ spl12_4
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f125,f109])).

fof(f125,plain,
    ( ~ l1_orders_2(sK0)
    | r2_hidden(sK6(sK0,sK1),sK1)
    | v1_waybel_0(sK1,sK0)
    | ~ spl12_8 ),
    inference(resolution,[],[f117,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK6(X0,X1),X1)
      | v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f149,plain,
    ( ~ spl12_11
    | spl12_12 ),
    inference(avatar_split_clause,[],[f54,f147,f144])).

fof(f54,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f118,plain,(
    spl12_8 ),
    inference(avatar_split_clause,[],[f59,f116])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f114,plain,(
    spl12_6 ),
    inference(avatar_split_clause,[],[f58,f112])).

fof(f58,plain,(
    v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f110,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f62,f108])).

fof(f62,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f106,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f61,f104])).

fof(f61,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f102,plain,(
    spl12_0 ),
    inference(avatar_split_clause,[],[f60,f100])).

fof(f60,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
