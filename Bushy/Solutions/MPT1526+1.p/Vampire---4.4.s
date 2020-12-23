%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t4_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:44 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 608 expanded)
%              Number of leaves         :   61 ( 261 expanded)
%              Depth                    :   10
%              Number of atoms          :  721 (2556 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f567,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f93,f100,f107,f114,f121,f134,f141,f148,f149,f168,f183,f197,f205,f214,f221,f250,f266,f276,f296,f303,f331,f359,f375,f377,f402,f409,f437,f444,f452,f462,f483,f495,f502,f513,f531,f547,f554,f566])).

fof(f566,plain,
    ( ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_46
    | spl8_63
    | ~ spl8_64 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_46
    | ~ spl8_63
    | ~ spl8_64 ),
    inference(subsumption_resolution,[],[f562,f564])).

fof(f564,plain,
    ( ~ r1_orders_2(sK0,sK2,sK5(sK0,sK3,sK1))
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_63
    | ~ spl8_64 ),
    inference(unit_resulting_resolution,[],[f85,f92,f120,f113,f106,f494,f501,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t4_yellow_0.p',t26_orders_2)).

fof(f501,plain,
    ( m1_subset_1(sK5(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ spl8_64 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl8_64
  <=> m1_subset_1(sK5(sK0,sK3,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f494,plain,
    ( ~ r1_orders_2(sK0,sK1,sK5(sK0,sK3,sK1))
    | ~ spl8_63 ),
    inference(avatar_component_clause,[],[f493])).

fof(f493,plain,
    ( spl8_63
  <=> ~ r1_orders_2(sK0,sK1,sK5(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f106,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl8_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f113,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl8_8
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f120,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl8_10
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f92,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl8_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f85,plain,
    ( v4_orders_2(sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl8_0
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f562,plain,
    ( r1_orders_2(sK0,sK2,sK5(sK0,sK3,sK1))
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_46
    | ~ spl8_64 ),
    inference(unit_resulting_resolution,[],[f92,f113,f127,f358,f501,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t4_yellow_0.p',d8_lattice3)).

fof(f358,plain,
    ( r2_hidden(sK5(sK0,sK3,sK1),sK3)
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl8_46
  <=> r2_hidden(sK5(sK0,sK3,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f127,plain,
    ( r1_lattice3(sK0,sK3,sK2)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_12
  <=> r1_lattice3(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f554,plain,
    ( spl8_70
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f534,f529,f552])).

fof(f552,plain,
    ( spl8_70
  <=> m1_subset_1(sK4(sK0,sK3,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f529,plain,
    ( spl8_66
  <=> r2_hidden(sK4(sK0,sK3,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f534,plain,
    ( m1_subset_1(sK4(sK0,sK3,sK1),sK3)
    | ~ spl8_66 ),
    inference(unit_resulting_resolution,[],[f530,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t4_yellow_0.p',t1_subset)).

fof(f530,plain,
    ( r2_hidden(sK4(sK0,sK3,sK1),sK3)
    | ~ spl8_66 ),
    inference(avatar_component_clause,[],[f529])).

fof(f547,plain,
    ( ~ spl8_69
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f533,f529,f545])).

fof(f545,plain,
    ( spl8_69
  <=> ~ r2_hidden(sK3,sK4(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).

fof(f533,plain,
    ( ~ r2_hidden(sK3,sK4(sK0,sK3,sK1))
    | ~ spl8_66 ),
    inference(unit_resulting_resolution,[],[f530,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t4_yellow_0.p',antisymmetry_r2_hidden)).

fof(f531,plain,
    ( spl8_66
    | ~ spl8_2
    | ~ spl8_6
    | spl8_15 ),
    inference(avatar_split_clause,[],[f516,f129,f105,f91,f529])).

fof(f129,plain,
    ( spl8_15
  <=> ~ r2_lattice3(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f516,plain,
    ( r2_hidden(sK4(sK0,sK3,sK1),sK3)
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f92,f106,f130,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t4_yellow_0.p',d9_lattice3)).

fof(f130,plain,
    ( ~ r2_lattice3(sK0,sK3,sK1)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f513,plain,
    ( ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | spl8_53
    | ~ spl8_58 ),
    inference(avatar_contradiction_clause,[],[f512])).

fof(f512,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_53
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f507,f511])).

fof(f511,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK3,sK2),sK1)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_53
    | ~ spl8_58 ),
    inference(unit_resulting_resolution,[],[f85,f92,f120,f106,f113,f436,f461,f72])).

fof(f461,plain,
    ( m1_subset_1(sK4(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f460])).

fof(f460,plain,
    ( spl8_58
  <=> m1_subset_1(sK4(sK0,sK3,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f436,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK3,sK2),sK2)
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl8_53
  <=> ~ r1_orders_2(sK0,sK4(sK0,sK3,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f507,plain,
    ( r1_orders_2(sK0,sK4(sK0,sK3,sK2),sK1)
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_58 ),
    inference(unit_resulting_resolution,[],[f92,f106,f133,f167,f461,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f167,plain,
    ( r2_hidden(sK4(sK0,sK3,sK2),sK3)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl8_20
  <=> r2_hidden(sK4(sK0,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f133,plain,
    ( r2_lattice3(sK0,sK3,sK1)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl8_14
  <=> r2_lattice3(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f502,plain,
    ( spl8_64
    | ~ spl8_2
    | ~ spl8_6
    | spl8_17 ),
    inference(avatar_split_clause,[],[f464,f139,f105,f91,f500])).

fof(f139,plain,
    ( spl8_17
  <=> ~ r1_lattice3(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f464,plain,
    ( m1_subset_1(sK5(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f92,f106,f140,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f140,plain,
    ( ~ r1_lattice3(sK0,sK3,sK1)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f139])).

fof(f495,plain,
    ( ~ spl8_63
    | ~ spl8_2
    | ~ spl8_6
    | spl8_17 ),
    inference(avatar_split_clause,[],[f463,f139,f105,f91,f493])).

fof(f463,plain,
    ( ~ r1_orders_2(sK0,sK1,sK5(sK0,sK3,sK1))
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f92,f106,f140,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f483,plain,
    ( ~ spl8_61
    | spl8_35
    | spl8_57 ),
    inference(avatar_split_clause,[],[f454,f447,f245,f481])).

fof(f481,plain,
    ( spl8_61
  <=> ~ m1_subset_1(sK4(sK0,k1_xboole_0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).

fof(f245,plain,
    ( spl8_35
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f447,plain,
    ( spl8_57
  <=> ~ r2_hidden(sK4(sK0,k1_xboole_0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f454,plain,
    ( ~ m1_subset_1(sK4(sK0,k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl8_35
    | ~ spl8_57 ),
    inference(unit_resulting_resolution,[],[f246,f448,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t4_yellow_0.p',t2_subset)).

fof(f448,plain,
    ( ~ r2_hidden(sK4(sK0,k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl8_57 ),
    inference(avatar_component_clause,[],[f447])).

fof(f246,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f245])).

fof(f462,plain,
    ( spl8_58
    | ~ spl8_2
    | ~ spl8_8
    | spl8_19 ),
    inference(avatar_split_clause,[],[f411,f146,f112,f91,f460])).

fof(f146,plain,
    ( spl8_19
  <=> ~ r2_lattice3(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f411,plain,
    ( m1_subset_1(sK4(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f92,f113,f147,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f147,plain,
    ( ~ r2_lattice3(sK0,sK3,sK2)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f146])).

fof(f452,plain,
    ( spl8_56
    | ~ spl8_2
    | ~ spl8_6
    | spl8_45 ),
    inference(avatar_split_clause,[],[f348,f326,f105,f91,f450])).

fof(f450,plain,
    ( spl8_56
  <=> r2_hidden(sK4(sK0,k1_xboole_0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f326,plain,
    ( spl8_45
  <=> ~ r2_lattice3(sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f348,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_45 ),
    inference(unit_resulting_resolution,[],[f92,f106,f327,f66])).

fof(f327,plain,
    ( ~ r2_lattice3(sK0,k1_xboole_0,sK1)
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f326])).

fof(f444,plain,
    ( ~ spl8_55
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f417,f166,f442])).

fof(f442,plain,
    ( spl8_55
  <=> ~ r2_hidden(sK3,sK4(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f417,plain,
    ( ~ r2_hidden(sK3,sK4(sK0,sK3,sK2))
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f167,f74])).

fof(f437,plain,
    ( ~ spl8_53
    | ~ spl8_2
    | ~ spl8_8
    | spl8_19 ),
    inference(avatar_split_clause,[],[f410,f146,f112,f91,f435])).

fof(f410,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK3,sK2),sK2)
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f92,f113,f147,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f409,plain,
    ( spl8_50
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f387,f357,f407])).

fof(f407,plain,
    ( spl8_50
  <=> m1_subset_1(sK5(sK0,sK3,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f387,plain,
    ( m1_subset_1(sK5(sK0,sK3,sK1),sK3)
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f358,f75])).

fof(f402,plain,
    ( ~ spl8_49
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f386,f357,f400])).

fof(f400,plain,
    ( spl8_49
  <=> ~ r2_hidden(sK3,sK5(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f386,plain,
    ( ~ r2_hidden(sK3,sK5(sK0,sK3,sK1))
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f358,f74])).

fof(f377,plain,
    ( ~ spl8_20
    | spl8_23 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f372,f176])).

fof(f176,plain,
    ( ~ m1_subset_1(sK4(sK0,sK3,sK2),sK3)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl8_23
  <=> ~ m1_subset_1(sK4(sK0,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f372,plain,
    ( m1_subset_1(sK4(sK0,sK3,sK2),sK3)
    | ~ spl8_20 ),
    inference(resolution,[],[f167,f75])).

fof(f375,plain,
    ( ~ spl8_20
    | spl8_23 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f368,f176])).

fof(f368,plain,
    ( m1_subset_1(sK4(sK0,sK3,sK2),sK3)
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f167,f75])).

fof(f359,plain,
    ( spl8_46
    | ~ spl8_2
    | ~ spl8_6
    | spl8_17 ),
    inference(avatar_split_clause,[],[f184,f139,f105,f91,f357])).

fof(f184,plain,
    ( r2_hidden(sK5(sK0,sK3,sK1),sK3)
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f92,f140,f106,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f331,plain,
    ( spl8_44
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f312,f248,f105,f91,f329])).

fof(f329,plain,
    ( spl8_44
  <=> r2_lattice3(sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f248,plain,
    ( spl8_34
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f312,plain,
    ( r2_lattice3(sK0,k1_xboole_0,sK1)
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_34 ),
    inference(unit_resulting_resolution,[],[f92,f106,f306,f66])).

fof(f306,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_34 ),
    inference(unit_resulting_resolution,[],[f249,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t4_yellow_0.p',t7_boole)).

fof(f249,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f248])).

fof(f303,plain,
    ( spl8_42
    | spl8_35 ),
    inference(avatar_split_clause,[],[f257,f245,f301])).

fof(f301,plain,
    ( spl8_42
  <=> r2_hidden(sK6(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f257,plain,
    ( r2_hidden(sK6(k1_xboole_0),k1_xboole_0)
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f73,f246,f76])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t4_yellow_0.p',existence_m1_subset_1)).

fof(f296,plain,
    ( ~ spl8_41
    | spl8_35 ),
    inference(avatar_split_clause,[],[f256,f245,f294])).

fof(f294,plain,
    ( spl8_41
  <=> ~ r2_hidden(k1_xboole_0,sK6(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f256,plain,
    ( ~ r2_hidden(k1_xboole_0,sK6(k1_xboole_0))
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f73,f246,f151])).

fof(f151,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f76,f74])).

fof(f276,plain,
    ( ~ spl8_39
    | spl8_37 ),
    inference(avatar_split_clause,[],[f267,f264,f274])).

fof(f274,plain,
    ( spl8_39
  <=> ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f264,plain,
    ( spl8_37
  <=> ~ m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f267,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl8_37 ),
    inference(unit_resulting_resolution,[],[f265,f75])).

fof(f265,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f264])).

fof(f266,plain,
    ( ~ spl8_37
    | spl8_35 ),
    inference(avatar_split_clause,[],[f255,f245,f264])).

fof(f255,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f246,f157])).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f151,f76])).

fof(f250,plain,
    ( spl8_34
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f235,f181,f248])).

fof(f181,plain,
    ( spl8_24
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f235,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_24 ),
    inference(backward_demodulation,[],[f225,f182])).

fof(f182,plain,
    ( v1_xboole_0(sK3)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f181])).

fof(f225,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_24 ),
    inference(unit_resulting_resolution,[],[f182,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t4_yellow_0.p',t6_boole)).

fof(f221,plain,
    ( spl8_32
    | spl8_25 ),
    inference(avatar_split_clause,[],[f188,f178,f219])).

fof(f219,plain,
    ( spl8_32
  <=> r2_hidden(sK6(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f178,plain,
    ( spl8_25
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f188,plain,
    ( r2_hidden(sK6(sK3),sK3)
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f73,f179,f76])).

fof(f179,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f178])).

fof(f214,plain,
    ( ~ spl8_31
    | spl8_25 ),
    inference(avatar_split_clause,[],[f187,f178,f212])).

fof(f212,plain,
    ( spl8_31
  <=> ~ r2_hidden(sK3,sK6(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f187,plain,
    ( ~ r2_hidden(sK3,sK6(sK3))
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f73,f179,f151])).

fof(f205,plain,
    ( ~ spl8_29
    | spl8_27 ),
    inference(avatar_split_clause,[],[f198,f195,f203])).

fof(f203,plain,
    ( spl8_29
  <=> ~ r2_hidden(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f195,plain,
    ( spl8_27
  <=> ~ m1_subset_1(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f198,plain,
    ( ~ r2_hidden(sK3,sK3)
    | ~ spl8_27 ),
    inference(unit_resulting_resolution,[],[f196,f75])).

fof(f196,plain,
    ( ~ m1_subset_1(sK3,sK3)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f195])).

fof(f197,plain,
    ( ~ spl8_27
    | spl8_25 ),
    inference(avatar_split_clause,[],[f186,f178,f195])).

fof(f186,plain,
    ( ~ m1_subset_1(sK3,sK3)
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f179,f157])).

fof(f183,plain,
    ( ~ spl8_23
    | spl8_24
    | spl8_21 ),
    inference(avatar_split_clause,[],[f170,f163,f181,f175])).

fof(f163,plain,
    ( spl8_21
  <=> ~ r2_hidden(sK4(sK0,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f170,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(sK4(sK0,sK3,sK2),sK3)
    | ~ spl8_21 ),
    inference(resolution,[],[f164,f76])).

fof(f164,plain,
    ( ~ r2_hidden(sK4(sK0,sK3,sK2),sK3)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f163])).

fof(f168,plain,
    ( spl8_20
    | ~ spl8_2
    | ~ spl8_8
    | spl8_19 ),
    inference(avatar_split_clause,[],[f160,f146,f112,f91,f166])).

fof(f160,plain,
    ( r2_hidden(sK4(sK0,sK3,sK2),sK3)
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f92,f147,f113,f66])).

fof(f149,plain,
    ( ~ spl8_17
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f62,f146,f139])).

fof(f62,plain,
    ( ~ r2_lattice3(sK0,sK3,sK2)
    | ~ r1_lattice3(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ( ~ r2_lattice3(sK0,sK3,sK2)
        & r2_lattice3(sK0,sK3,sK1) )
      | ( ~ r1_lattice3(sK0,sK3,sK1)
        & r1_lattice3(sK0,sK3,sK2) ) )
    & r1_orders_2(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f40,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r2_lattice3(X0,X3,X2)
                      & r2_lattice3(X0,X3,X1) )
                    | ( ~ r1_lattice3(X0,X3,X1)
                      & r1_lattice3(X0,X3,X2) ) )
                & r1_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(sK0,X3,X2)
                    & r2_lattice3(sK0,X3,X1) )
                  | ( ~ r1_lattice3(sK0,X3,X1)
                    & r1_lattice3(sK0,X3,X2) ) )
              & r1_orders_2(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(X0,X3,X2)
                    & r2_lattice3(X0,X3,X1) )
                  | ( ~ r1_lattice3(X0,X3,X1)
                    & r1_lattice3(X0,X3,X2) ) )
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r2_lattice3(X0,X3,X2)
                  & r2_lattice3(X0,X3,sK1) )
                | ( ~ r1_lattice3(X0,X3,sK1)
                  & r1_lattice3(X0,X3,X2) ) )
            & r1_orders_2(X0,sK1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r2_lattice3(X0,X3,X2)
                & r2_lattice3(X0,X3,X1) )
              | ( ~ r1_lattice3(X0,X3,X1)
                & r1_lattice3(X0,X3,X2) ) )
          & r1_orders_2(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ( ~ r2_lattice3(X0,X3,sK2)
              & r2_lattice3(X0,X3,X1) )
            | ( ~ r1_lattice3(X0,X3,X1)
              & r1_lattice3(X0,X3,sK2) ) )
        & r1_orders_2(X0,X1,sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X3,X2)
            & r2_lattice3(X0,X3,X1) )
          | ( ~ r1_lattice3(X0,X3,X1)
            & r1_lattice3(X0,X3,X2) ) )
     => ( ( ~ r2_lattice3(X0,sK3,X2)
          & r2_lattice3(X0,sK3,X1) )
        | ( ~ r1_lattice3(X0,sK3,X1)
          & r1_lattice3(X0,sK3,X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(X0,X3,X2)
                    & r2_lattice3(X0,X3,X1) )
                  | ( ~ r1_lattice3(X0,X3,X1)
                    & r1_lattice3(X0,X3,X2) ) )
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(X0,X3,X2)
                    & r2_lattice3(X0,X3,X1) )
                  | ( ~ r1_lattice3(X0,X3,X1)
                    & r1_lattice3(X0,X3,X2) ) )
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_orders_2(X0,X1,X2)
                 => ! [X3] :
                      ( ( r2_lattice3(X0,X3,X1)
                       => r2_lattice3(X0,X3,X2) )
                      & ( r1_lattice3(X0,X3,X2)
                       => r1_lattice3(X0,X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
               => ! [X3] :
                    ( ( r2_lattice3(X0,X3,X1)
                     => r2_lattice3(X0,X3,X2) )
                    & ( r1_lattice3(X0,X3,X2)
                     => r1_lattice3(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t4_yellow_0.p',t4_yellow_0)).

fof(f148,plain,
    ( spl8_12
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f61,f146,f126])).

fof(f61,plain,
    ( ~ r2_lattice3(sK0,sK3,sK2)
    | r1_lattice3(sK0,sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f141,plain,
    ( ~ spl8_17
    | spl8_14 ),
    inference(avatar_split_clause,[],[f60,f132,f139])).

fof(f60,plain,
    ( r2_lattice3(sK0,sK3,sK1)
    | ~ r1_lattice3(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f134,plain,
    ( spl8_12
    | spl8_14 ),
    inference(avatar_split_clause,[],[f59,f132,f126])).

fof(f59,plain,
    ( r2_lattice3(sK0,sK3,sK1)
    | r1_lattice3(sK0,sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f121,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f58,f119])).

fof(f58,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f114,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f57,f112])).

fof(f57,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f107,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f56,f105])).

fof(f56,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f79,f98])).

fof(f98,plain,
    ( spl8_4
  <=> l1_orders_2(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f79,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    l1_orders_2(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f11,f52])).

fof(f52,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK7) ),
    introduced(choice_axiom,[])).

fof(f11,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t4_yellow_0.p',existence_l1_orders_2)).

fof(f93,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f55,f91])).

fof(f55,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f86,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f54,f84])).

fof(f54,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
