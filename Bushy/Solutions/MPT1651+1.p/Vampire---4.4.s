%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t31_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:48 EDT 2019

% Result     : Theorem 1.98s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 345 expanded)
%              Number of leaves         :   27 ( 121 expanded)
%              Depth                    :   20
%              Number of atoms          :  769 (1467 expanded)
%              Number of equality atoms :    4 (  16 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3221,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f117,f124,f131,f155,f162,f187,f223,f259,f262,f272,f453,f473,f2661,f3000,f3010,f3204,f3219])).

fof(f3219,plain,
    ( ~ spl11_6
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_28
    | spl11_269 ),
    inference(avatar_contradiction_clause,[],[f3218])).

fof(f3218,plain,
    ( $false
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_28
    | ~ spl11_269 ),
    inference(subsumption_resolution,[],[f3216,f258])).

fof(f258,plain,
    ( r2_hidden(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),k3_waybel_0(sK0,sK1))
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl11_28
  <=> r2_hidden(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),k3_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f3216,plain,
    ( ~ r2_hidden(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),k3_waybel_0(sK0,sK1))
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_269 ),
    inference(resolution,[],[f3203,f424])).

fof(f424,plain,
    ( ! [X1] :
        ( sP4(X1,sK1,sK0)
        | ~ r2_hidden(X1,k3_waybel_0(sK0,sK1)) )
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f234,f230])).

fof(f230,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k3_waybel_0(sK0,sK1))
        | m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl11_24 ),
    inference(resolution,[],[f222,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t31_waybel_0.p',t4_subset)).

fof(f222,plain,
    ( m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl11_24
  <=> m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f234,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP4(X1,sK1,sK0)
        | ~ r2_hidden(X1,k3_waybel_0(sK0,sK1)) )
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f233,f130])).

fof(f130,plain,
    ( l1_orders_2(sK0)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl11_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f233,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP4(X1,sK1,sK0)
        | ~ r2_hidden(X1,k3_waybel_0(sK0,sK1)) )
    | ~ spl11_10
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f227,f161])).

fof(f161,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl11_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f227,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP4(X1,sK1,sK0)
        | ~ r2_hidden(X1,k3_waybel_0(sK0,sK1)) )
    | ~ spl11_24 ),
    inference(resolution,[],[f222,f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP4(X3,X1,X0)
      | ~ r2_hidden(X3,k3_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t31_waybel_0.p',d15_waybel_0)).

fof(f3203,plain,
    ( ~ sP4(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),sK1,sK0)
    | ~ spl11_269 ),
    inference(avatar_component_clause,[],[f3202])).

fof(f3202,plain,
    ( spl11_269
  <=> ~ sP4(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_269])])).

fof(f3204,plain,
    ( ~ spl11_269
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_16
    | spl11_19
    | ~ spl11_232 ),
    inference(avatar_split_clause,[],[f3185,f2659,f182,f179,f153,f129,f122,f3202])).

fof(f122,plain,
    ( spl11_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f153,plain,
    ( spl11_8
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f179,plain,
    ( spl11_16
  <=> r2_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f182,plain,
    ( spl11_19
  <=> ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f2659,plain,
    ( spl11_232
  <=> m1_subset_1(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_232])])).

fof(f3185,plain,
    ( ~ sP4(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),sK1,sK0)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_232 ),
    inference(resolution,[],[f3116,f180])).

fof(f180,plain,
    ( r2_lattice3(sK0,sK1,sK2)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f179])).

fof(f3116,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,X0,sK2)
        | ~ sP4(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),X0,sK0) )
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_19
    | ~ spl11_232 ),
    inference(duplicate_literal_removal,[],[f3113])).

fof(f3113,plain,
    ( ! [X0] :
        ( ~ sP4(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),X0,sK0)
        | ~ r2_lattice3(sK0,X0,sK2)
        | ~ sP4(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),X0,sK0) )
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_19
    | ~ spl11_232 ),
    inference(resolution,[],[f3065,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3065,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK5(sK0,X2,sK6(sK0,k3_waybel_0(sK0,sK1),sK2)),X3)
        | ~ sP4(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),X2,sK0)
        | ~ r2_lattice3(sK0,X3,sK2) )
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_19
    | ~ spl11_232 ),
    inference(subsumption_resolution,[],[f3064,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))
      | ~ sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3064,plain,
    ( ! [X2,X3] :
        ( ~ sP4(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),X2,sK0)
        | ~ m1_subset_1(sK5(sK0,X2,sK6(sK0,k3_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK0,X2,sK6(sK0,k3_waybel_0(sK0,sK1),sK2)),X3)
        | ~ r2_lattice3(sK0,X3,sK2) )
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_19
    | ~ spl11_232 ),
    inference(subsumption_resolution,[],[f3060,f154])).

fof(f154,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f153])).

fof(f3060,plain,
    ( ! [X2,X3] :
        ( ~ sP4(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),X2,sK0)
        | ~ m1_subset_1(sK5(sK0,X2,sK6(sK0,k3_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK0,X2,sK6(sK0,k3_waybel_0(sK0,sK1),sK2)),X3)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X3,sK2) )
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_19
    | ~ spl11_232 ),
    inference(resolution,[],[f3043,f134])).

fof(f134,plain,
    ( ! [X6,X4,X5] :
        ( r1_orders_2(sK0,X5,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,X6)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X6,X4) )
    | ~ spl11_6 ),
    inference(resolution,[],[f130,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t31_waybel_0.p',d9_lattice3)).

fof(f3043,plain,
    ( ! [X5] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X5,sK6(sK0,k3_waybel_0(sK0,sK1),sK2)),sK2)
        | ~ sP4(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),X5,sK0) )
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_19
    | ~ spl11_232 ),
    inference(subsumption_resolution,[],[f3036,f65])).

fof(f3036,plain,
    ( ! [X5] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X5,sK6(sK0,k3_waybel_0(sK0,sK1),sK2)),sK2)
        | ~ m1_subset_1(sK5(sK0,X5,sK6(sK0,k3_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
        | ~ sP4(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),X5,sK0) )
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_19
    | ~ spl11_232 ),
    inference(resolution,[],[f3017,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r1_orders_2(X0,X3,sK5(X0,X1,X3))
      | ~ sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3017,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK6(sK0,k3_waybel_0(sK0,sK1),sK2),X0)
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_19
    | ~ spl11_232 ),
    inference(subsumption_resolution,[],[f3016,f2660])).

fof(f2660,plain,
    ( m1_subset_1(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ spl11_232 ),
    inference(avatar_component_clause,[],[f2659])).

fof(f3016,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK6(sK0,k3_waybel_0(sK0,sK1),sK2),X0)
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f3013,f154])).

fof(f3013,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK6(sK0,k3_waybel_0(sK0,sK1),sK2),X0)
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_19 ),
    inference(resolution,[],[f183,f225])).

fof(f225,plain,
    ( ! [X2,X0,X1] :
        ( r2_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK6(sK0,X2,X1),X0)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(sK6(sK0,X2,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_4
    | ~ spl11_6 ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK6(sK0,X2,X1),X0)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(sK6(sK0,X2,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X2,X1) )
    | ~ spl11_4
    | ~ spl11_6 ),
    inference(resolution,[],[f142,f136])).

fof(f136,plain,
    ( ! [X10,X9] :
        ( ~ r1_orders_2(sK0,sK6(sK0,X10,X9),X9)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | r2_lattice3(sK0,X10,X9) )
    | ~ spl11_6 ),
    inference(resolution,[],[f130,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f142,plain,
    ( ! [X12,X13,X11] :
        ( r1_orders_2(sK0,X11,X13)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X11,X12)
        | ~ r1_orders_2(sK0,X12,X13)
        | ~ m1_subset_1(X11,u1_struct_0(sK0)) )
    | ~ spl11_4
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f137,f123])).

fof(f123,plain,
    ( v4_orders_2(sK0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f137,plain,
    ( ! [X12,X13,X11] :
        ( ~ v4_orders_2(sK0)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X11,X12)
        | ~ r1_orders_2(sK0,X12,X13)
        | r1_orders_2(sK0,X11,X13) )
    | ~ spl11_6 ),
    inference(resolution,[],[f130,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t31_waybel_0.p',t26_orders_2)).

fof(f183,plain,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f182])).

fof(f3010,plain,
    ( ~ spl11_18
    | ~ spl11_60
    | ~ spl11_254 ),
    inference(avatar_contradiction_clause,[],[f3009])).

fof(f3009,plain,
    ( $false
    | ~ spl11_18
    | ~ spl11_60
    | ~ spl11_254 ),
    inference(subsumption_resolution,[],[f3002,f186])).

fof(f186,plain,
    ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl11_18
  <=> r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f3002,plain,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ~ spl11_60
    | ~ spl11_254 ),
    inference(resolution,[],[f2999,f452])).

fof(f452,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK6(sK0,sK1,sK2),X1)
        | ~ r2_lattice3(sK0,X1,sK2) )
    | ~ spl11_60 ),
    inference(avatar_component_clause,[],[f451])).

fof(f451,plain,
    ( spl11_60
  <=> ! [X1] :
        ( ~ r2_hidden(sK6(sK0,sK1,sK2),X1)
        | ~ r2_lattice3(sK0,X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_60])])).

fof(f2999,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),k3_waybel_0(sK0,sK1))
    | ~ spl11_254 ),
    inference(avatar_component_clause,[],[f2998])).

fof(f2998,plain,
    ( spl11_254
  <=> r2_hidden(sK6(sK0,sK1,sK2),k3_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_254])])).

fof(f3000,plain,
    ( spl11_254
    | spl11_1
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_30
    | ~ spl11_58 ),
    inference(avatar_split_clause,[],[f2993,f445,f270,f221,f160,f129,f115,f108,f2998])).

fof(f108,plain,
    ( spl11_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f115,plain,
    ( spl11_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f270,plain,
    ( spl11_30
  <=> r2_hidden(sK6(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f445,plain,
    ( spl11_58
  <=> m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f2993,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),k3_waybel_0(sK0,sK1))
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_30
    | ~ spl11_58 ),
    inference(subsumption_resolution,[],[f2992,f446])).

fof(f446,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl11_58 ),
    inference(avatar_component_clause,[],[f445])).

fof(f2992,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | r2_hidden(sK6(sK0,sK1,sK2),k3_waybel_0(sK0,sK1))
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_30
    | ~ spl11_58 ),
    inference(duplicate_literal_removal,[],[f2989])).

fof(f2989,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | r2_hidden(sK6(sK0,sK1,sK2),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_30
    | ~ spl11_58 ),
    inference(resolution,[],[f2777,f148])).

fof(f148,plain,
    ( ! [X19] :
        ( r3_orders_2(sK0,X19,X19)
        | ~ m1_subset_1(X19,u1_struct_0(sK0)) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f147,f109])).

fof(f109,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f147,plain,
    ( ! [X19] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | r3_orders_2(sK0,X19,X19) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f141,f116])).

fof(f116,plain,
    ( v3_orders_2(sK0)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f141,plain,
    ( ! [X19] :
        ( ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | r3_orders_2(sK0,X19,X19) )
    | ~ spl11_6 ),
    inference(resolution,[],[f130,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1) ) ),
    inference(condensation,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t31_waybel_0.p',reflexivity_r3_orders_2)).

fof(f2777,plain,
    ( ! [X4] :
        ( ~ r3_orders_2(sK0,X4,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_hidden(X4,k3_waybel_0(sK0,sK1)) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_30
    | ~ spl11_58 ),
    inference(subsumption_resolution,[],[f2772,f446])).

fof(f2772,plain,
    ( ! [X4] :
        ( r2_hidden(X4,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X4,sK6(sK0,sK1,sK2)) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_30
    | ~ spl11_58 ),
    inference(duplicate_literal_removal,[],[f2771])).

fof(f2771,plain,
    ( ! [X4] :
        ( r2_hidden(X4,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X4,sK6(sK0,sK1,sK2)) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_30
    | ~ spl11_58 ),
    inference(resolution,[],[f2706,f146])).

fof(f146,plain,
    ( ! [X17,X18] :
        ( r1_orders_2(sK0,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X17,X18) )
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f145,f109])).

fof(f145,plain,
    ( ! [X17,X18] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | r1_orders_2(sK0,X17,X18)
        | ~ r3_orders_2(sK0,X17,X18) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f140,f116])).

fof(f140,plain,
    ( ! [X17,X18] :
        ( ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | r1_orders_2(sK0,X17,X18)
        | ~ r3_orders_2(sK0,X17,X18) )
    | ~ spl11_6 ),
    inference(resolution,[],[f130,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t31_waybel_0.p',redefinition_r3_orders_2)).

fof(f2706,plain,
    ( ! [X5] :
        ( ~ r1_orders_2(sK0,X5,sK6(sK0,sK1,sK2))
        | r2_hidden(X5,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_30
    | ~ spl11_58 ),
    inference(subsumption_resolution,[],[f2703,f446])).

fof(f2703,plain,
    ( ! [X5] :
        ( r2_hidden(X5,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,X5,sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0)) )
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_30 ),
    inference(resolution,[],[f417,f271])).

fof(f271,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),sK1)
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f270])).

fof(f417,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_24 ),
    inference(resolution,[],[f232,f64])).

fof(f64,plain,(
    ! [X4,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r1_orders_2(X0,X3,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ sP4(X0,sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k3_waybel_0(sK0,sK1)) )
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f231,f130])).

fof(f231,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP4(X0,sK1,sK0)
        | r2_hidden(X0,k3_waybel_0(sK0,sK1)) )
    | ~ spl11_10
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f226,f161])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP4(X0,sK1,sK0)
        | r2_hidden(X0,k3_waybel_0(sK0,sK1)) )
    | ~ spl11_24 ),
    inference(resolution,[],[f222,f102])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP4(X3,X1,X0)
      | r2_hidden(X3,k3_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2661,plain,
    ( spl11_232
    | ~ spl11_24
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f2604,f257,f221,f2659])).

fof(f2604,plain,
    ( m1_subset_1(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ spl11_24
    | ~ spl11_28 ),
    inference(resolution,[],[f258,f230])).

fof(f473,plain,
    ( ~ spl11_6
    | ~ spl11_8
    | spl11_17
    | spl11_59 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_17
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f471,f177])).

fof(f177,plain,
    ( ~ r2_lattice3(sK0,sK1,sK2)
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl11_17
  <=> ~ r2_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f471,plain,
    ( r2_lattice3(sK0,sK1,sK2)
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f470,f130])).

fof(f470,plain,
    ( ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK2)
    | ~ spl11_8
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f467,f154])).

fof(f467,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK2)
    | ~ spl11_59 ),
    inference(resolution,[],[f449,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f449,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl11_59 ),
    inference(avatar_component_clause,[],[f448])).

fof(f448,plain,
    ( spl11_59
  <=> ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_59])])).

fof(f453,plain,
    ( ~ spl11_59
    | spl11_60
    | ~ spl11_6
    | ~ spl11_8
    | spl11_17 ),
    inference(avatar_split_clause,[],[f358,f176,f153,f129,f451,f448])).

fof(f358,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK6(sK0,sK1,sK2),X1)
        | ~ r2_lattice3(sK0,X1,sK2)
        | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0)) )
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f355,f154])).

fof(f355,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK6(sK0,sK1,sK2),X1)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,sK2)
        | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0)) )
    | ~ spl11_6
    | ~ spl11_17 ),
    inference(resolution,[],[f177,f216])).

fof(f216,plain,
    ( ! [X2,X0,X1] :
        ( r2_lattice3(sK0,X0,X1)
        | ~ r2_hidden(sK6(sK0,X0,X1),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) )
    | ~ spl11_6 ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r2_hidden(sK6(sK0,X0,X1),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl11_6 ),
    inference(resolution,[],[f134,f136])).

fof(f272,plain,
    ( spl11_30
    | ~ spl11_6
    | ~ spl11_8
    | spl11_17 ),
    inference(avatar_split_clause,[],[f265,f176,f153,f129,f270])).

fof(f265,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),sK1)
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f264,f154])).

fof(f264,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_6
    | ~ spl11_17 ),
    inference(resolution,[],[f177,f135])).

fof(f135,plain,
    ( ! [X8,X7] :
        ( r2_lattice3(sK0,X8,X7)
        | r2_hidden(sK6(sK0,X8,X7),X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
    | ~ spl11_6 ),
    inference(resolution,[],[f130,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f262,plain,
    ( ~ spl11_16
    | ~ spl11_18 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f260,f186])).

fof(f260,plain,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f54,f180])).

fof(f54,plain,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ~ r2_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_lattice3(X0,X1,X2)
              <~> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_lattice3(X0,X1,X2)
              <~> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X2)
                <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_lattice3(X0,X1,X2)
              <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t31_waybel_0.p',t31_waybel_0)).

fof(f259,plain,
    ( spl11_28
    | ~ spl11_6
    | ~ spl11_8
    | spl11_19 ),
    inference(avatar_split_clause,[],[f204,f182,f153,f129,f257])).

fof(f204,plain,
    ( r2_hidden(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),k3_waybel_0(sK0,sK1))
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f203,f154])).

fof(f203,plain,
    ( r2_hidden(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_6
    | ~ spl11_19 ),
    inference(resolution,[],[f135,f183])).

fof(f223,plain,
    ( spl11_24
    | ~ spl11_6
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f194,f160,f129,f221])).

fof(f194,plain,
    ( m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_6
    | ~ spl11_10 ),
    inference(resolution,[],[f138,f161])).

fof(f138,plain,
    ( ! [X14] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k3_waybel_0(sK0,X14),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_6 ),
    inference(resolution,[],[f130,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t31_waybel_0.p',dt_k3_waybel_0)).

fof(f187,plain,
    ( spl11_16
    | spl11_18 ),
    inference(avatar_split_clause,[],[f53,f185,f179])).

fof(f53,plain,
    ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | r2_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f162,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f56,f160])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f155,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f55,f153])).

fof(f55,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f131,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f60,f129])).

fof(f60,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f124,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f59,f122])).

fof(f59,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f117,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f58,f115])).

fof(f58,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f110,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f57,f108])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
