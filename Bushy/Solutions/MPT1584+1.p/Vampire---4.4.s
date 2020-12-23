%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t63_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:46 EDT 2019

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 388 expanded)
%              Number of leaves         :   25 ( 138 expanded)
%              Depth                    :   13
%              Number of atoms          :  659 (1864 expanded)
%              Number of equality atoms :   15 (  93 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4001,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f95,f103,f107,f112,f146,f162,f174,f175,f490,f635,f3867,f3884,f3887,f3889,f3899,f3967,f3992,f3995,f4000])).

fof(f4000,plain,
    ( ~ spl10_0
    | ~ spl10_8
    | spl10_19
    | ~ spl10_148 ),
    inference(avatar_contradiction_clause,[],[f3999])).

fof(f3999,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_8
    | ~ spl10_19
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f3998,f158])).

fof(f158,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl10_19
  <=> ~ r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f3998,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl10_0
    | ~ spl10_8
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f3997,f85])).

fof(f85,plain,
    ( l1_orders_2(sK0)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl10_0
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f3997,plain,
    ( ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK2,sK3)
    | ~ spl10_8
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f3996,f106])).

fof(f106,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl10_8
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f3996,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK2,sK3)
    | ~ spl10_148 ),
    inference(resolution,[],[f3988,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t63_yellow_0.p',d9_lattice3)).

fof(f3988,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK2,sK3),sK3)
    | ~ spl10_148 ),
    inference(avatar_component_clause,[],[f3987])).

fof(f3987,plain,
    ( spl10_148
  <=> r1_orders_2(sK0,sK5(sK0,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_148])])).

fof(f3995,plain,
    ( ~ spl10_0
    | ~ spl10_8
    | spl10_19
    | spl10_151 ),
    inference(avatar_contradiction_clause,[],[f3994])).

fof(f3994,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_8
    | ~ spl10_19
    | ~ spl10_151 ),
    inference(subsumption_resolution,[],[f3993,f158])).

fof(f3993,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl10_0
    | ~ spl10_8
    | ~ spl10_151 ),
    inference(resolution,[],[f3991,f124])).

fof(f124,plain,
    ( ! [X6] :
        ( m1_subset_1(sK5(sK0,X6,sK3),u1_struct_0(sK0))
        | r2_lattice3(sK0,X6,sK3) )
    | ~ spl10_0
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f117,f85])).

fof(f117,plain,
    ( ! [X6] :
        ( ~ l1_orders_2(sK0)
        | m1_subset_1(sK5(sK0,X6,sK3),u1_struct_0(sK0))
        | r2_lattice3(sK0,X6,sK3) )
    | ~ spl10_8 ),
    inference(resolution,[],[f106,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3991,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl10_151 ),
    inference(avatar_component_clause,[],[f3990])).

fof(f3990,plain,
    ( spl10_151
  <=> ~ m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_151])])).

fof(f3992,plain,
    ( spl10_148
    | ~ spl10_151
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_74
    | ~ spl10_146 ),
    inference(avatar_split_clause,[],[f3985,f3965,f498,f110,f105,f93,f84,f3990,f3987])).

fof(f93,plain,
    ( spl10_4
  <=> m1_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f110,plain,
    ( spl10_10
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f498,plain,
    ( spl10_74
  <=> m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).

fof(f3965,plain,
    ( spl10_146
  <=> r1_orders_2(sK1,sK5(sK0,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_146])])).

fof(f3985,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK5(sK0,sK2,sK3),sK3)
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_74
    | ~ spl10_146 ),
    inference(subsumption_resolution,[],[f3984,f111])).

fof(f111,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f3984,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK5(sK0,sK2,sK3),sK3)
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_74
    | ~ spl10_146 ),
    inference(subsumption_resolution,[],[f3983,f499])).

fof(f499,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK1))
    | ~ spl10_74 ),
    inference(avatar_component_clause,[],[f498])).

fof(f3983,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK5(sK0,sK2,sK3),sK3)
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_146 ),
    inference(subsumption_resolution,[],[f3982,f106])).

fof(f3982,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK5(sK0,sK2,sK3),sK3)
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_146 ),
    inference(resolution,[],[f3966,f99])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1) )
    | ~ spl10_0
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f97,f85])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X0,X1)
        | r1_orders_2(sK0,X0,X1) )
    | ~ spl10_4 ),
    inference(resolution,[],[f94,f77])).

fof(f77,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X4,X5)
      | r1_orders_2(X0,X4,X5) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X3 != X5
      | ~ r1_orders_2(X1,X4,X5)
      | r1_orders_2(X0,X4,X3) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X2 != X4
      | X3 != X5
      | ~ r1_orders_2(X1,X4,X5)
      | r1_orders_2(X0,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X4,X5)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X0,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t63_yellow_0.p',t60_yellow_0)).

fof(f94,plain,
    ( m1_yellow_0(sK1,sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f3966,plain,
    ( r1_orders_2(sK1,sK5(sK0,sK2,sK3),sK3)
    | ~ spl10_146 ),
    inference(avatar_component_clause,[],[f3965])).

fof(f3967,plain,
    ( spl10_146
    | ~ spl10_0
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | spl10_19
    | ~ spl10_26
    | ~ spl10_74 ),
    inference(avatar_split_clause,[],[f3949,f498,f172,f157,f110,f105,f101,f84,f3965])).

fof(f101,plain,
    ( spl10_6
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f172,plain,
    ( spl10_26
  <=> r2_lattice3(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f3949,plain,
    ( r1_orders_2(sK1,sK5(sK0,sK2,sK3),sK3)
    | ~ spl10_0
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_19
    | ~ spl10_26
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f3948,f111])).

fof(f3948,plain,
    ( r1_orders_2(sK1,sK5(sK0,sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_19
    | ~ spl10_26
    | ~ spl10_74 ),
    inference(resolution,[],[f3900,f173])).

fof(f173,plain,
    ( r2_lattice3(sK1,sK2,sK3)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f172])).

fof(f3900,plain,
    ( ! [X2] :
        ( ~ r2_lattice3(sK1,sK2,X2)
        | r1_orders_2(sK1,sK5(sK0,sK2,sK3),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    | ~ spl10_0
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_19
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f3877,f158])).

fof(f3877,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r1_orders_2(sK1,sK5(sK0,sK2,sK3),X2)
        | ~ r2_lattice3(sK1,sK2,X2)
        | r2_lattice3(sK0,sK2,sK3) )
    | ~ spl10_0
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_74 ),
    inference(resolution,[],[f1046,f125])).

fof(f125,plain,
    ( ! [X7] :
        ( r2_hidden(sK5(sK0,X7,sK3),X7)
        | r2_lattice3(sK0,X7,sK3) )
    | ~ spl10_0
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f118,f85])).

fof(f118,plain,
    ( ! [X7] :
        ( ~ l1_orders_2(sK0)
        | r2_hidden(sK5(sK0,X7,sK3),X7)
        | r2_lattice3(sK0,X7,sK3) )
    | ~ spl10_8 ),
    inference(resolution,[],[f106,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1046,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(sK5(sK0,sK2,sK3),X5)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r1_orders_2(sK1,sK5(sK0,sK2,sK3),X4)
        | ~ r2_lattice3(sK1,X5,X4) )
    | ~ spl10_6
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f1039,f102])).

fof(f102,plain,
    ( l1_orders_2(sK1)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f1039,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | ~ r2_hidden(sK5(sK0,sK2,sK3),X5)
        | r1_orders_2(sK1,sK5(sK0,sK2,sK3),X4)
        | ~ r2_lattice3(sK1,X5,X4) )
    | ~ spl10_74 ),
    inference(resolution,[],[f499,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3899,plain,
    ( ~ spl10_0
    | ~ spl10_8
    | spl10_21
    | ~ spl10_138 ),
    inference(avatar_contradiction_clause,[],[f3898])).

fof(f3898,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_8
    | ~ spl10_21
    | ~ spl10_138 ),
    inference(subsumption_resolution,[],[f3897,f161])).

fof(f161,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl10_21
  <=> ~ r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f3897,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl10_0
    | ~ spl10_8
    | ~ spl10_138 ),
    inference(subsumption_resolution,[],[f3896,f85])).

fof(f3896,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl10_8
    | ~ spl10_138 ),
    inference(subsumption_resolution,[],[f3895,f106])).

fof(f3895,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl10_138 ),
    inference(resolution,[],[f3880,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t63_yellow_0.p',d8_lattice3)).

fof(f3880,plain,
    ( r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3))
    | ~ spl10_138 ),
    inference(avatar_component_clause,[],[f3879])).

fof(f3879,plain,
    ( spl10_138
  <=> r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_138])])).

fof(f3889,plain,
    ( ~ spl10_19
    | spl10_24 ),
    inference(avatar_split_clause,[],[f79,f169,f157])).

fof(f169,plain,
    ( spl10_24
  <=> r1_lattice3(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f79,plain,
    ( r1_lattice3(sK1,sK2,sK3)
    | ~ r2_lattice3(sK0,sK2,sK3) ),
    inference(forward_demodulation,[],[f49,f51])).

fof(f51,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( ~ r2_lattice3(X0,X2,X3)
                          & r2_lattice3(X1,X2,X4) )
                        | ( ~ r1_lattice3(X0,X2,X3)
                          & r1_lattice3(X1,X2,X4) ) )
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( ~ r2_lattice3(X0,X2,X3)
                          & r2_lattice3(X1,X2,X4) )
                        | ( ~ r1_lattice3(X0,X2,X3)
                          & r1_lattice3(X1,X2,X4) ) )
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_yellow_0(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ( X3 = X4
                         => ( ( r2_lattice3(X1,X2,X4)
                             => r2_lattice3(X0,X2,X3) )
                            & ( r1_lattice3(X1,X2,X4)
                             => r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ( X3 = X4
                         => ( ( r2_lattice3(X1,X2,X4)
                             => r2_lattice3(X0,X2,X3) )
                            & ( r1_lattice3(X1,X2,X4)
                             => r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( X3 = X4
                       => ( ( r2_lattice3(X1,X2,X4)
                           => r2_lattice3(X0,X2,X3) )
                          & ( r1_lattice3(X1,X2,X4)
                           => r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t63_yellow_0.p',t63_yellow_0)).

fof(f49,plain,
    ( r1_lattice3(sK1,sK2,sK4)
    | ~ r2_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f3887,plain,
    ( ~ spl10_0
    | ~ spl10_8
    | spl10_21
    | spl10_141 ),
    inference(avatar_contradiction_clause,[],[f3886])).

fof(f3886,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_8
    | ~ spl10_21
    | ~ spl10_141 ),
    inference(subsumption_resolution,[],[f3885,f161])).

fof(f3885,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl10_0
    | ~ spl10_8
    | ~ spl10_141 ),
    inference(resolution,[],[f3883,f121])).

fof(f121,plain,
    ( ! [X2] :
        ( m1_subset_1(sK6(sK0,X2,sK3),u1_struct_0(sK0))
        | r1_lattice3(sK0,X2,sK3) )
    | ~ spl10_0
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f114,f85])).

fof(f114,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | m1_subset_1(sK6(sK0,X2,sK3),u1_struct_0(sK0))
        | r1_lattice3(sK0,X2,sK3) )
    | ~ spl10_8 ),
    inference(resolution,[],[f106,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3883,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl10_141 ),
    inference(avatar_component_clause,[],[f3882])).

fof(f3882,plain,
    ( spl10_141
  <=> ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_141])])).

fof(f3884,plain,
    ( spl10_138
    | ~ spl10_141
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_72
    | ~ spl10_136 ),
    inference(avatar_split_clause,[],[f3874,f3865,f488,f110,f105,f93,f84,f3882,f3879])).

fof(f488,plain,
    ( spl10_72
  <=> m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f3865,plain,
    ( spl10_136
  <=> r1_orders_2(sK1,sK3,sK6(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_136])])).

fof(f3874,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3))
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_72
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f3873,f106])).

fof(f3873,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3))
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_72
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f3872,f489])).

fof(f489,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK1))
    | ~ spl10_72 ),
    inference(avatar_component_clause,[],[f488])).

fof(f3872,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3))
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_136 ),
    inference(subsumption_resolution,[],[f3871,f111])).

fof(f3871,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3))
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_136 ),
    inference(resolution,[],[f3866,f99])).

fof(f3866,plain,
    ( r1_orders_2(sK1,sK3,sK6(sK0,sK2,sK3))
    | ~ spl10_136 ),
    inference(avatar_component_clause,[],[f3865])).

fof(f3867,plain,
    ( spl10_136
    | ~ spl10_0
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | spl10_21
    | ~ spl10_24
    | ~ spl10_72 ),
    inference(avatar_split_clause,[],[f3858,f488,f169,f160,f110,f105,f101,f84,f3865])).

fof(f3858,plain,
    ( r1_orders_2(sK1,sK3,sK6(sK0,sK2,sK3))
    | ~ spl10_0
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_21
    | ~ spl10_24
    | ~ spl10_72 ),
    inference(subsumption_resolution,[],[f3857,f111])).

fof(f3857,plain,
    ( r1_orders_2(sK1,sK3,sK6(sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_21
    | ~ spl10_24
    | ~ spl10_72 ),
    inference(resolution,[],[f3856,f170])).

fof(f170,plain,
    ( r1_lattice3(sK1,sK2,sK3)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f169])).

fof(f3856,plain,
    ( ! [X2] :
        ( ~ r1_lattice3(sK1,sK2,X2)
        | r1_orders_2(sK1,X2,sK6(sK0,sK2,sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    | ~ spl10_0
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_21
    | ~ spl10_72 ),
    inference(subsumption_resolution,[],[f3854,f161])).

fof(f3854,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r1_orders_2(sK1,X2,sK6(sK0,sK2,sK3))
        | ~ r1_lattice3(sK1,sK2,X2)
        | r1_lattice3(sK0,sK2,sK3) )
    | ~ spl10_0
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_72 ),
    inference(resolution,[],[f513,f122])).

fof(f122,plain,
    ( ! [X3] :
        ( r2_hidden(sK6(sK0,X3,sK3),X3)
        | r1_lattice3(sK0,X3,sK3) )
    | ~ spl10_0
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f115,f85])).

fof(f115,plain,
    ( ! [X3] :
        ( ~ l1_orders_2(sK0)
        | r2_hidden(sK6(sK0,X3,sK3),X3)
        | r1_lattice3(sK0,X3,sK3) )
    | ~ spl10_8 ),
    inference(resolution,[],[f106,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f513,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK6(sK0,sK2,sK3),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK1,X0,sK6(sK0,sK2,sK3))
        | ~ r1_lattice3(sK1,X1,X0) )
    | ~ spl10_6
    | ~ spl10_72 ),
    inference(subsumption_resolution,[],[f506,f102])).

fof(f506,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | ~ r2_hidden(sK6(sK0,sK2,sK3),X1)
        | r1_orders_2(sK1,X0,sK6(sK0,sK2,sK3))
        | ~ r1_lattice3(sK1,X1,X0) )
    | ~ spl10_72 ),
    inference(resolution,[],[f489,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f635,plain,
    ( spl10_74
    | spl10_18
    | ~ spl10_0
    | ~ spl10_8
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f473,f144,f105,f84,f633,f498])).

fof(f633,plain,
    ( spl10_18
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f144,plain,
    ( spl10_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f473,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_8
    | ~ spl10_14 ),
    inference(resolution,[],[f231,f145])).

fof(f145,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f231,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
        | r2_lattice3(sK0,X2,sK3)
        | m1_subset_1(sK5(sK0,X2,sK3),X3) )
    | ~ spl10_0
    | ~ spl10_8 ),
    inference(resolution,[],[f125,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t63_yellow_0.p',t4_subset)).

fof(f490,plain,
    ( spl10_72
    | ~ spl10_0
    | ~ spl10_8
    | ~ spl10_14
    | spl10_21 ),
    inference(avatar_split_clause,[],[f468,f160,f144,f105,f84,f488])).

fof(f468,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f462,f161])).

fof(f462,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_8
    | ~ spl10_14 ),
    inference(resolution,[],[f222,f145])).

fof(f222,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
        | r1_lattice3(sK0,X2,sK3)
        | m1_subset_1(sK6(sK0,X2,sK3),X3) )
    | ~ spl10_0
    | ~ spl10_8 ),
    inference(resolution,[],[f122,f70])).

fof(f175,plain,
    ( ~ spl10_21
    | spl10_26 ),
    inference(avatar_split_clause,[],[f82,f172,f160])).

fof(f82,plain,
    ( r2_lattice3(sK1,sK2,sK3)
    | ~ r1_lattice3(sK0,sK2,sK3) ),
    inference(forward_demodulation,[],[f46,f51])).

fof(f46,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f174,plain,
    ( spl10_24
    | spl10_26 ),
    inference(avatar_split_clause,[],[f81,f172,f169])).

fof(f81,plain,
    ( r2_lattice3(sK1,sK2,sK3)
    | r1_lattice3(sK1,sK2,sK3) ),
    inference(forward_demodulation,[],[f80,f51])).

fof(f80,plain,
    ( r1_lattice3(sK1,sK2,sK3)
    | r2_lattice3(sK1,sK2,sK4) ),
    inference(forward_demodulation,[],[f48,f51])).

fof(f48,plain,
    ( r1_lattice3(sK1,sK2,sK4)
    | r2_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f162,plain,
    ( ~ spl10_19
    | ~ spl10_21 ),
    inference(avatar_split_clause,[],[f47,f160,f157])).

fof(f47,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f146,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f53,f144])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f112,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f78,f110])).

fof(f78,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f50,f51])).

fof(f50,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f107,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f52,f105])).

fof(f52,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f103,plain,
    ( spl10_6
    | ~ spl10_0
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f98,f93,f84,f101])).

fof(f98,plain,
    ( l1_orders_2(sK1)
    | ~ spl10_0
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f96,f85])).

fof(f96,plain,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK1)
    | ~ spl10_4 ),
    inference(resolution,[],[f94,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t63_yellow_0.p',dt_m1_yellow_0)).

fof(f95,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f54,f93])).

fof(f54,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    spl10_0 ),
    inference(avatar_split_clause,[],[f55,f84])).

fof(f55,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
