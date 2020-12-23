%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t12_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:44 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 332 expanded)
%              Number of leaves         :   25 ( 121 expanded)
%              Depth                    :   31
%              Number of atoms          :  845 (1678 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f324,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f100,f107,f114,f127,f134,f138,f142,f146,f150,f154,f170,f176,f265,f285,f286,f303,f313,f323])).

fof(f323,plain,
    ( spl12_1
    | spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_10
    | ~ spl12_16
    | ~ spl12_30
    | ~ spl12_32 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_10
    | ~ spl12_16
    | ~ spl12_30
    | ~ spl12_32 ),
    inference(subsumption_resolution,[],[f321,f319])).

fof(f319,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_10
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f318,f99])).

fof(f99,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl12_3
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f318,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_10
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f317,f126])).

fof(f126,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl12_10
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f317,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f316,f113])).

fof(f113,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl12_6
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f316,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f315,f92])).

fof(f92,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl12_1
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f315,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl12_4
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f314,f106])).

fof(f106,plain,
    ( l1_orders_2(sK0)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl12_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f314,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl12_30 ),
    inference(resolution,[],[f296,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_orders_2(X1,X3,X4)
                 => r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2)) ) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t12_waybel_0.p',s1_waybel_0__e1_35_1__waybel_0)).

fof(f296,plain,
    ( r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2))
    | ~ spl12_30 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl12_30
  <=> r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f321,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl12_16
    | ~ spl12_32 ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl12_16
    | ~ spl12_32 ),
    inference(resolution,[],[f302,f141])).

fof(f141,plain,
    ( ! [X3] :
        ( r1_orders_2(sK1,X3,sK4(X3))
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl12_16
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_orders_2(sK1,X3,sK4(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f302,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK1,sK6(sK0,sK1,sK2),sK4(X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl12_32 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl12_32
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK6(sK0,sK1,sK2),sK4(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).

fof(f313,plain,
    ( spl12_1
    | spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_10
    | spl12_31 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_31 ),
    inference(subsumption_resolution,[],[f311,f117])).

fof(f117,plain,
    ( v11_waybel_0(sK1,sK0)
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl12_8
  <=> v11_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f311,plain,
    ( ~ v11_waybel_0(sK1,sK0)
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_10
    | ~ spl12_31 ),
    inference(subsumption_resolution,[],[f310,f99])).

fof(f310,plain,
    ( v2_struct_0(sK0)
    | ~ v11_waybel_0(sK1,sK0)
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_10
    | ~ spl12_31 ),
    inference(subsumption_resolution,[],[f309,f126])).

fof(f309,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ v11_waybel_0(sK1,sK0)
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_31 ),
    inference(subsumption_resolution,[],[f308,f113])).

fof(f308,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ v11_waybel_0(sK1,sK0)
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_31 ),
    inference(subsumption_resolution,[],[f307,f92])).

fof(f307,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ v11_waybel_0(sK1,sK0)
    | ~ spl12_4
    | ~ spl12_31 ),
    inference(subsumption_resolution,[],[f306,f106])).

fof(f306,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ v11_waybel_0(sK1,sK0)
    | ~ spl12_31 ),
    inference(resolution,[],[f299,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v11_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v11_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( v11_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t12_waybel_0.p',d14_waybel_0)).

fof(f299,plain,
    ( ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2))
    | ~ spl12_31 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl12_31
  <=> ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).

fof(f303,plain,
    ( ~ spl12_31
    | spl12_32
    | spl12_1
    | spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_10
    | ~ spl12_14
    | ~ spl12_20 ),
    inference(avatar_split_clause,[],[f293,f148,f136,f125,f112,f105,f98,f91,f301,f298])).

fof(f136,plain,
    ( spl12_14
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK1))
        | m1_subset_1(sK4(X3),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f148,plain,
    ( spl12_20
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK4(X3)),k2_waybel_0(sK0,sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK6(sK0,sK1,sK2),sK4(X0))
        | ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2)) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_10
    | ~ spl12_14
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f292,f137])).

fof(f137,plain,
    ( ! [X3] :
        ( m1_subset_1(sK4(X3),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f136])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK6(sK0,sK1,sK2),sK4(X0))
        | ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2)) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_10
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f291,f99])).

fof(f291,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK6(sK0,sK1,sK2),sK4(X0))
        | v2_struct_0(sK0)
        | ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2)) )
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_10
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f290,f126])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK6(sK0,sK1,sK2),sK4(X0))
        | v2_struct_0(sK0)
        | ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2)) )
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f289,f113])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK6(sK0,sK1,sK2),sK4(X0))
        | v2_struct_0(sK0)
        | ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2)) )
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f288,f92])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK6(sK0,sK1,sK2),sK4(X0))
        | v2_struct_0(sK0)
        | ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2)) )
    | ~ spl12_4
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f287,f106])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4(X0),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK6(sK0,sK1,sK2),sK4(X0))
        | v2_struct_0(sK0)
        | ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2)) )
    | ~ spl12_20 ),
    inference(resolution,[],[f149,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X1,sK6(X0,X1,X2),X4)
      | v2_struct_0(X0)
      | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f149,plain,
    ( ! [X3] :
        ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK4(X3)),k2_waybel_0(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f148])).

fof(f286,plain,
    ( spl12_8
    | spl12_1
    | spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | spl12_29 ),
    inference(avatar_split_clause,[],[f283,f263,f112,f105,f98,f91,f116])).

fof(f263,plain,
    ( spl12_29
  <=> ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).

fof(f283,plain,
    ( v11_waybel_0(sK1,sK0)
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_29 ),
    inference(subsumption_resolution,[],[f282,f99])).

fof(f282,plain,
    ( v2_struct_0(sK0)
    | v11_waybel_0(sK1,sK0)
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_29 ),
    inference(subsumption_resolution,[],[f281,f113])).

fof(f281,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | v11_waybel_0(sK1,sK0)
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_29 ),
    inference(subsumption_resolution,[],[f280,f92])).

fof(f280,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | v11_waybel_0(sK1,sK0)
    | ~ spl12_4
    | ~ spl12_29 ),
    inference(subsumption_resolution,[],[f279,f106])).

fof(f279,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | v11_waybel_0(sK1,sK0)
    | ~ spl12_29 ),
    inference(resolution,[],[f264,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK9(X0,X1),u1_struct_0(X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | v11_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f264,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK1))
    | ~ spl12_29 ),
    inference(avatar_component_clause,[],[f263])).

fof(f285,plain,
    ( spl12_1
    | spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | spl12_9
    | spl12_29 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_9
    | ~ spl12_29 ),
    inference(subsumption_resolution,[],[f283,f120])).

fof(f120,plain,
    ( ~ v11_waybel_0(sK1,sK0)
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl12_9
  <=> ~ v11_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f265,plain,
    ( ~ spl12_29
    | spl12_1
    | spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | spl12_9
    | ~ spl12_18
    | ~ spl12_22 ),
    inference(avatar_split_clause,[],[f246,f152,f144,f119,f112,f105,f98,f91,f263])).

fof(f144,plain,
    ( spl12_18
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK1))
        | m1_subset_1(sK3(X2),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f152,plain,
    ( spl12_22
  <=> ! [X2,X4] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X4),k2_waybel_0(sK0,sK1,X2))
        | ~ r1_orders_2(sK1,sK3(X2),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f246,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK1))
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_9
    | ~ spl12_18
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f245,f120])).

fof(f245,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK1))
    | v11_waybel_0(sK1,sK0)
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_18
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f244,f99])).

fof(f244,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | v11_waybel_0(sK1,sK0)
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_18
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f243,f113])).

fof(f243,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | v11_waybel_0(sK1,sK0)
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_18
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f242,f92])).

fof(f242,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | v11_waybel_0(sK1,sK0)
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_18
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f239,f106])).

fof(f239,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | v11_waybel_0(sK1,sK0)
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_18
    | ~ spl12_22 ),
    inference(resolution,[],[f233,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,sK9(X0,X1)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | v11_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f233,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_18
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f232,f145])).

fof(f145,plain,
    ( ! [X2] :
        ( m1_subset_1(sK3(X2),u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f144])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1)) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_18
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f231,f99])).

fof(f231,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_18
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f230,f106])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_18
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f229,f113])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_18
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f228,f92])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_18
    | ~ spl12_22 ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_18
    | ~ spl12_22 ),
    inference(resolution,[],[f225,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X1))
      | r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7(sK0,sK1,X0,sK3(X0)),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0)) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_18
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f224,f145])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK7(sK0,sK1,X0,sK3(X0)),u1_struct_0(sK1)) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f223,f99])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK7(sK0,sK1,X0,sK3(X0)),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f222,f106])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK7(sK0,sK1,X0,sK3(X0)),u1_struct_0(sK1))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f221,f113])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK7(sK0,sK1,X0,sK3(X0)),u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f220,f92])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK7(sK0,sK1,X0,sK3(X0)),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_22 ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK7(sK0,sK1,X0,sK3(X0)),u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_22 ),
    inference(resolution,[],[f206,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X3,sK7(X0,X1,X2,X3))
      | r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,sK3(X0),sK7(sK0,sK1,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK7(sK0,sK1,X0,X1),u1_struct_0(sK1)) )
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f205,f99])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ r1_orders_2(sK1,sK3(X0),sK7(sK0,sK1,X0,X1))
        | ~ m1_subset_1(sK7(sK0,sK1,X0,X1),u1_struct_0(sK1)) )
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f204,f113])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ r1_orders_2(sK1,sK3(X0),sK7(sK0,sK1,X0,X1))
        | ~ m1_subset_1(sK7(sK0,sK1,X0,X1),u1_struct_0(sK1)) )
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f203,f92])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ r1_orders_2(sK1,sK3(X0),sK7(sK0,sK1,X0,X1))
        | ~ m1_subset_1(sK7(sK0,sK1,X0,X1),u1_struct_0(sK1)) )
    | ~ spl12_4
    | ~ spl12_22 ),
    inference(subsumption_resolution,[],[f202,f106])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ r1_orders_2(sK1,sK3(X0),sK7(sK0,sK1,X0,X1))
        | ~ m1_subset_1(sK7(sK0,sK1,X0,X1),u1_struct_0(sK1)) )
    | ~ spl12_22 ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK3(X0),sK7(sK0,sK1,X0,X1))
        | ~ m1_subset_1(sK7(sK0,sK1,X0,X1),u1_struct_0(sK1)) )
    | ~ spl12_22 ),
    inference(resolution,[],[f70,f153])).

fof(f153,plain,
    ( ! [X4,X2] :
        ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X4),k2_waybel_0(sK0,sK1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK3(X2),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f152])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,sK7(X0,X1,X2,X3)),k2_waybel_0(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f176,plain,
    ( ~ spl12_4
    | spl12_27 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl12_4
    | ~ spl12_27 ),
    inference(subsumption_resolution,[],[f174,f106])).

fof(f174,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl12_27 ),
    inference(resolution,[],[f169,f85])).

fof(f85,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t12_waybel_0.p',dt_l1_orders_2)).

fof(f169,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl12_27 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl12_27
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_27])])).

fof(f170,plain,
    ( spl12_24
    | ~ spl12_27
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f155,f112,f168,f162])).

fof(f162,plain,
    ( spl12_24
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f155,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK1)
    | ~ spl12_6 ),
    inference(resolution,[],[f83,f113])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t12_waybel_0.p',dt_l1_waybel_0)).

fof(f154,plain,
    ( spl12_8
    | spl12_22 ),
    inference(avatar_split_clause,[],[f57,f152,f116])).

fof(f57,plain,(
    ! [X4,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,sK3(X2),X4)
      | r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X4),k2_waybel_0(sK0,sK1,X2))
      | v11_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v11_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v11_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( v11_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X1))
                 => ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => ( r1_orders_2(X1,X3,X4)
                           => r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2)) ) )
                      & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( v11_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ( r1_orders_2(X1,X3,X4)
                         => r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2)) ) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t12_waybel_0.p',t12_waybel_0)).

fof(f150,plain,
    ( ~ spl12_9
    | spl12_20 ),
    inference(avatar_split_clause,[],[f56,f148,f119])).

fof(f56,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK4(X3)),k2_waybel_0(sK0,sK1,sK2))
      | ~ v11_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f146,plain,
    ( spl12_8
    | spl12_18 ),
    inference(avatar_split_clause,[],[f58,f144,f116])).

fof(f58,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | m1_subset_1(sK3(X2),u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f142,plain,
    ( ~ spl12_9
    | spl12_16 ),
    inference(avatar_split_clause,[],[f55,f140,f119])).

fof(f55,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK1))
      | r1_orders_2(sK1,X3,sK4(X3))
      | ~ v11_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f138,plain,
    ( ~ spl12_9
    | spl12_14 ),
    inference(avatar_split_clause,[],[f54,f136,f119])).

fof(f54,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK1))
      | m1_subset_1(sK4(X3),u1_struct_0(sK1))
      | ~ v11_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f134,plain,(
    spl12_12 ),
    inference(avatar_split_clause,[],[f84,f132])).

fof(f132,plain,
    ( spl12_12
  <=> l1_orders_2(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f84,plain,(
    l1_orders_2(sK11) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t12_waybel_0.p',existence_l1_orders_2)).

fof(f127,plain,
    ( ~ spl12_9
    | spl12_10 ),
    inference(avatar_split_clause,[],[f59,f125,f119])).

fof(f59,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v11_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f114,plain,(
    spl12_6 ),
    inference(avatar_split_clause,[],[f61,f112])).

fof(f61,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f107,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f63,f105])).

fof(f63,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f100,plain,(
    ~ spl12_3 ),
    inference(avatar_split_clause,[],[f62,f98])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f60,f91])).

fof(f60,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
