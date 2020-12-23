%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1526+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 317 expanded)
%              Number of leaves         :   11 (  72 expanded)
%              Depth                    :   21
%              Number of atoms          :  399 (1852 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f494,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f274,f387,f422,f475,f487,f493])).

fof(f493,plain,
    ( ~ spl6_4
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f492,f37,f47])).

fof(f47,plain,
    ( spl6_4
  <=> r2_lattice3(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f37,plain,
    ( spl6_2
  <=> r1_lattice3(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f492,plain,
    ( ~ r2_lattice3(sK0,sK3,sK2)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f15,f38])).

fof(f38,plain,
    ( r1_lattice3(sK0,sK3,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f15,plain,
    ( ~ r1_lattice3(sK0,sK3,sK1)
    | ~ r2_lattice3(sK0,sK3,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).

fof(f487,plain,
    ( spl6_4
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | spl6_4
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f485,f49])).

fof(f49,plain,
    ( ~ r2_lattice3(sK0,sK3,sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f485,plain,
    ( r2_lattice3(sK0,sK3,sK2)
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f484,f22])).

fof(f22,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f484,plain,
    ( ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK3,sK2)
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f482,f18])).

fof(f18,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f482,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK3,sK2)
    | ~ spl6_18 ),
    inference(resolution,[],[f479,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f479,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK3,sK2),sK2)
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f476,f18])).

fof(f476,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK3,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_18 ),
    inference(resolution,[],[f474,f19])).

fof(f19,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f474,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK1,X0)
        | r1_orders_2(sK0,sK5(sK0,sK3,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f473])).

fof(f473,plain,
    ( spl6_18
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK5(sK0,sK3,sK2),X0)
        | ~ r1_orders_2(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f475,plain,
    ( spl6_18
    | ~ spl6_14
    | ~ spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f433,f47,f33,f412,f473])).

fof(f412,plain,
    ( spl6_14
  <=> m1_subset_1(sK5(sK0,sK3,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f33,plain,
    ( spl6_1
  <=> r2_lattice3(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f433,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK3,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | r1_orders_2(sK0,sK5(sK0,sK3,sK2),X0) )
    | ~ spl6_1
    | spl6_4 ),
    inference(subsumption_resolution,[],[f432,f21])).

fof(f21,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f432,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK3,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | r1_orders_2(sK0,sK5(sK0,sK3,sK2),X0) )
    | ~ spl6_1
    | spl6_4 ),
    inference(subsumption_resolution,[],[f431,f20])).

fof(f20,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f431,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK3,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | r1_orders_2(sK0,sK5(sK0,sK3,sK2),X0) )
    | ~ spl6_1
    | spl6_4 ),
    inference(subsumption_resolution,[],[f430,f22])).

fof(f430,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK5(sK0,sK3,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | r1_orders_2(sK0,sK5(sK0,sK3,sK2),X0) )
    | ~ spl6_1
    | spl6_4 ),
    inference(resolution,[],[f429,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(f429,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK3,sK2),sK1)
    | ~ spl6_1
    | spl6_4 ),
    inference(subsumption_resolution,[],[f428,f49])).

fof(f428,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK3,sK2),sK1)
    | r2_lattice3(sK0,sK3,sK2)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f427,f20])).

fof(f427,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK3,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_lattice3(sK0,sK3,sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f349,f35])).

fof(f35,plain,
    ( r2_lattice3(sK0,sK3,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f349,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,X1,X0)
      | r1_orders_2(sK0,sK5(sK0,X1,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,X1,sK2) ) ),
    inference(duplicate_literal_removal,[],[f348])).

fof(f348,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,sK5(sK0,X1,sK2),X0)
      | ~ r2_lattice3(sK0,X1,X0)
      | r2_lattice3(sK0,X1,sK2)
      | r2_lattice3(sK0,X1,sK2) ) ),
    inference(resolution,[],[f220,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK0,X0,sK2),X0)
      | r2_lattice3(sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f55,f22])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | r2_hidden(sK5(sK0,X0,sK2),X0)
      | r2_lattice3(sK0,X0,sK2) ) ),
    inference(resolution,[],[f29,f18])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f220,plain,(
    ! [X30,X31,X29] :
      ( ~ r2_hidden(sK5(sK0,X30,sK2),X31)
      | ~ m1_subset_1(X29,u1_struct_0(sK0))
      | r1_orders_2(sK0,sK5(sK0,X30,sK2),X29)
      | ~ r2_lattice3(sK0,X31,X29)
      | r2_lattice3(sK0,X30,sK2) ) ),
    inference(subsumption_resolution,[],[f206,f22])).

fof(f206,plain,(
    ! [X30,X31,X29] :
      ( ~ m1_subset_1(X29,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(sK5(sK0,X30,sK2),X31)
      | r1_orders_2(sK0,sK5(sK0,X30,sK2),X29)
      | ~ r2_lattice3(sK0,X31,X29)
      | r2_lattice3(sK0,X30,sK2) ) ),
    inference(resolution,[],[f27,f93])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,X0,sK2),u1_struct_0(sK0))
      | r2_lattice3(sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f87,f22])).

fof(f87,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | m1_subset_1(sK5(sK0,X0,sK2),u1_struct_0(sK0))
      | r2_lattice3(sK0,X0,sK2) ) ),
    inference(resolution,[],[f28,f18])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f422,plain,
    ( spl6_4
    | spl6_14 ),
    inference(avatar_contradiction_clause,[],[f421])).

fof(f421,plain,
    ( $false
    | spl6_4
    | spl6_14 ),
    inference(subsumption_resolution,[],[f420,f49])).

fof(f420,plain,
    ( r2_lattice3(sK0,sK3,sK2)
    | spl6_14 ),
    inference(resolution,[],[f414,f93])).

fof(f414,plain,
    ( ~ m1_subset_1(sK5(sK0,sK3,sK2),u1_struct_0(sK0))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f412])).

fof(f387,plain,
    ( spl6_2
    | ~ spl6_3
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | spl6_2
    | ~ spl6_3
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f385,f39])).

fof(f39,plain,
    ( ~ r1_lattice3(sK0,sK3,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f385,plain,
    ( r1_lattice3(sK0,sK3,sK1)
    | spl6_2
    | ~ spl6_3
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f384,f22])).

fof(f384,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK3,sK1)
    | spl6_2
    | ~ spl6_3
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f381,f20])).

fof(f381,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK3,sK1)
    | spl6_2
    | ~ spl6_3
    | ~ spl6_10 ),
    inference(resolution,[],[f375,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(f375,plain,
    ( r1_orders_2(sK0,sK1,sK4(sK0,sK3,sK1))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f372,f268])).

fof(f268,plain,
    ( m1_subset_1(sK4(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl6_10
  <=> m1_subset_1(sK4(sK0,sK3,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f372,plain,
    ( ~ m1_subset_1(sK4(sK0,sK3,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK4(sK0,sK3,sK1))
    | spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f364,f253])).

fof(f253,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f252,f21])).

fof(f252,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ r1_orders_2(sK0,sK2,X0)
      | r1_orders_2(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f251,f18])).

fof(f251,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ r1_orders_2(sK0,sK2,X0)
      | r1_orders_2(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f250,f20])).

fof(f250,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ r1_orders_2(sK0,sK2,X0)
      | r1_orders_2(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f249,f22])).

fof(f249,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ r1_orders_2(sK0,sK2,X0)
      | r1_orders_2(sK0,sK1,X0) ) ),
    inference(resolution,[],[f31,f19])).

fof(f364,plain,
    ( r1_orders_2(sK0,sK2,sK4(sK0,sK3,sK1))
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f363,f39])).

fof(f363,plain,
    ( r1_orders_2(sK0,sK2,sK4(sK0,sK3,sK1))
    | r1_lattice3(sK0,sK3,sK1)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f358,f18])).

fof(f358,plain,
    ( r1_orders_2(sK0,sK2,sK4(sK0,sK3,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK3,sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f44,f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK0,X1,X0)
      | r1_orders_2(sK0,X0,sK4(sK0,X1,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattice3(sK0,X1,sK1) ) ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,sK4(sK0,X1,sK1))
      | ~ r1_lattice3(sK0,X1,X0)
      | r1_lattice3(sK0,X1,sK1)
      | r1_lattice3(sK0,X1,sK1) ) ),
    inference(resolution,[],[f179,f54])).

fof(f54,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1,sK1),X1)
      | r1_lattice3(sK0,X1,sK1) ) ),
    inference(subsumption_resolution,[],[f52,f22])).

fof(f52,plain,(
    ! [X1] :
      ( ~ l1_orders_2(sK0)
      | r2_hidden(sK4(sK0,X1,sK1),X1)
      | r1_lattice3(sK0,X1,sK1) ) ),
    inference(resolution,[],[f25,f20])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f179,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK4(sK0,X5,sK1),X6)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r1_orders_2(sK0,X4,sK4(sK0,X5,sK1))
      | ~ r1_lattice3(sK0,X6,X4)
      | r1_lattice3(sK0,X5,sK1) ) ),
    inference(subsumption_resolution,[],[f165,f22])).

fof(f165,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(sK4(sK0,X5,sK1),X6)
      | r1_orders_2(sK0,X4,sK4(sK0,X5,sK1))
      | ~ r1_lattice3(sK0,X6,X4)
      | r1_lattice3(sK0,X5,sK1) ) ),
    inference(resolution,[],[f23,f62])).

fof(f62,plain,(
    ! [X1] :
      ( m1_subset_1(sK4(sK0,X1,sK1),u1_struct_0(sK0))
      | r1_lattice3(sK0,X1,sK1) ) ),
    inference(subsumption_resolution,[],[f60,f22])).

fof(f60,plain,(
    ! [X1] :
      ( ~ l1_orders_2(sK0)
      | m1_subset_1(sK4(sK0,X1,sK1),u1_struct_0(sK0))
      | r1_lattice3(sK0,X1,sK1) ) ),
    inference(resolution,[],[f24,f20])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,
    ( r1_lattice3(sK0,sK3,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl6_3
  <=> r1_lattice3(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f274,plain,
    ( spl6_2
    | spl6_10 ),
    inference(avatar_split_clause,[],[f271,f267,f37])).

fof(f271,plain,
    ( r1_lattice3(sK0,sK3,sK1)
    | spl6_10 ),
    inference(resolution,[],[f269,f62])).

fof(f269,plain,
    ( ~ m1_subset_1(sK4(sK0,sK3,sK1),u1_struct_0(sK0))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f267])).

fof(f50,plain,
    ( ~ spl6_4
    | spl6_3 ),
    inference(avatar_split_clause,[],[f17,f42,f47])).

fof(f17,plain,
    ( r1_lattice3(sK0,sK3,sK2)
    | ~ r2_lattice3(sK0,sK3,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f45,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f16,f42,f33])).

fof(f16,plain,
    ( r1_lattice3(sK0,sK3,sK2)
    | r2_lattice3(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f40,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f14,f37,f33])).

fof(f14,plain,
    ( ~ r1_lattice3(sK0,sK3,sK1)
    | r2_lattice3(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
