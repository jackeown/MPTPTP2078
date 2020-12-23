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
% DateTime   : Thu Dec  3 13:15:36 EST 2020

% Result     : Theorem 3.20s
% Output     : Refutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 639 expanded)
%              Number of leaves         :   27 ( 222 expanded)
%              Depth                    :   38
%              Number of atoms          : 1617 (3603 expanded)
%              Number of equality atoms :  125 ( 211 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3011,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f92,f121,f126,f132,f137,f167,f182,f1852,f1988,f2010,f2754,f2755,f2963,f3009,f3010])).

fof(f3010,plain,
    ( ~ spl9_54
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_50 ),
    inference(avatar_split_clause,[],[f2969,f2960,f123,f118,f89,f79,f74,f3006])).

fof(f3006,plain,
    ( spl9_54
  <=> r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f74,plain,
    ( spl9_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f79,plain,
    ( spl9_3
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f89,plain,
    ( spl9_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f118,plain,
    ( spl9_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f123,plain,
    ( spl9_7
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f2960,plain,
    ( spl9_50
  <=> r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f2969,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_50 ),
    inference(subsumption_resolution,[],[f2968,f125])).

fof(f125,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f2968,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6
    | spl9_50 ),
    inference(subsumption_resolution,[],[f2967,f120])).

fof(f120,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f2967,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_50 ),
    inference(superposition,[],[f2962,f145])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( k10_lattice3(sK0,X0,X1) = k13_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f144,f91])).

fof(f91,plain,
    ( l1_orders_2(sK0)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X0,X1) = k13_lattice3(sK0,X0,X1) )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f93,f81])).

fof(f81,plain,
    ( v1_lattice3(sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X0,X1) = k13_lattice3(sK0,X0,X1) )
    | ~ spl9_2 ),
    inference(resolution,[],[f76,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f76,plain,
    ( v5_orders_2(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f2962,plain,
    ( ~ r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | spl9_50 ),
    inference(avatar_component_clause,[],[f2960])).

fof(f3009,plain,
    ( spl9_54
    | ~ spl9_38
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f2822,f2751,f1985,f3006])).

fof(f1985,plain,
    ( spl9_38
  <=> r1_orders_2(sK0,sK1,sK5(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f2751,plain,
    ( spl9_46
  <=> k10_lattice3(sK0,sK1,sK2) = sK5(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f2822,plain,
    ( r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ spl9_38
    | ~ spl9_46 ),
    inference(superposition,[],[f1987,f2753])).

fof(f2753,plain,
    ( k10_lattice3(sK0,sK1,sK2) = sK5(sK0,sK2,sK1)
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f2751])).

fof(f1987,plain,
    ( r1_orders_2(sK0,sK1,sK5(sK0,sK2,sK1))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f1985])).

fof(f2963,plain,
    ( ~ spl9_50
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_9
    | ~ spl9_11
    | spl9_12 ),
    inference(avatar_split_clause,[],[f2819,f164,f160,f134,f123,f89,f84,f74,f69,f2960])).

fof(f69,plain,
    ( spl9_1
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f84,plain,
    ( spl9_4
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f134,plain,
    ( spl9_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f160,plain,
    ( spl9_11
  <=> m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f164,plain,
    ( spl9_12
  <=> sK1 = k11_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f2819,plain,
    ( ~ r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_9
    | ~ spl9_11
    | spl9_12 ),
    inference(subsumption_resolution,[],[f2769,f161])).

fof(f161,plain,
    ( m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f160])).

fof(f2769,plain,
    ( ~ r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_9
    | spl9_12 ),
    inference(subsumption_resolution,[],[f255,f125])).

fof(f255,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9
    | spl9_12 ),
    inference(trivial_inequality_removal,[],[f246])).

fof(f246,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9
    | spl9_12 ),
    inference(superposition,[],[f166,f221])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( k11_lattice3(sK0,X1,X0) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f220,f138])).

fof(f138,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f116,f136])).

fof(f136,plain,
    ( ~ v2_struct_0(sK0)
    | spl9_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f116,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X0) )
    | ~ spl9_1
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f112,f71])).

fof(f71,plain,
    ( v3_orders_2(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X0) )
    | ~ spl9_5 ),
    inference(resolution,[],[f91,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f220,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | k11_lattice3(sK0,X1,X0) = X1 )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k11_lattice3(sK0,X1,X0) = X1
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k11_lattice3(sK0,X1,X0) = X1 )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f200,f191])).

fof(f191,plain,
    ( ! [X4,X2,X3] :
        ( r1_orders_2(sK0,sK7(sK0,X2,X3,X4),X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X2)
        | ~ r1_orders_2(sK0,X4,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k11_lattice3(sK0,X2,X3) = X4 )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f190,f91])).

fof(f190,plain,
    ( ! [X4,X2,X3] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X2)
        | ~ r1_orders_2(sK0,X4,X3)
        | r1_orders_2(sK0,sK7(sK0,X2,X3,X4),X2)
        | k11_lattice3(sK0,X2,X3) = X4 )
    | ~ spl9_2
    | ~ spl9_4
    | spl9_9 ),
    inference(subsumption_resolution,[],[f109,f136])).

fof(f109,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X2)
        | ~ r1_orders_2(sK0,X4,X3)
        | r1_orders_2(sK0,sK7(sK0,X2,X3,X4),X2)
        | k11_lattice3(sK0,X2,X3) = X4 )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f105,f76])).

fof(f105,plain,
    ( ! [X4,X2,X3] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X2)
        | ~ r1_orders_2(sK0,X4,X3)
        | r1_orders_2(sK0,sK7(sK0,X2,X3,X4),X2)
        | k11_lattice3(sK0,X2,X3) = X4 )
    | ~ spl9_4 ),
    inference(resolution,[],[f86,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(f86,plain,
    ( v2_lattice3(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f200,plain,
    ( ! [X10,X8,X9] :
        ( ~ r1_orders_2(sK0,sK7(sK0,X8,X9,X10),X10)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X10,X8)
        | ~ r1_orders_2(sK0,X10,X9)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | k11_lattice3(sK0,X8,X9) = X10 )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f199,f91])).

fof(f199,plain,
    ( ! [X10,X8,X9] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X10,X8)
        | ~ r1_orders_2(sK0,X10,X9)
        | ~ r1_orders_2(sK0,sK7(sK0,X8,X9,X10),X10)
        | k11_lattice3(sK0,X8,X9) = X10 )
    | ~ spl9_2
    | ~ spl9_4
    | spl9_9 ),
    inference(subsumption_resolution,[],[f111,f136])).

fof(f111,plain,
    ( ! [X10,X8,X9] :
        ( v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X10,X8)
        | ~ r1_orders_2(sK0,X10,X9)
        | ~ r1_orders_2(sK0,sK7(sK0,X8,X9,X10),X10)
        | k11_lattice3(sK0,X8,X9) = X10 )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f107,f76])).

fof(f107,plain,
    ( ! [X10,X8,X9] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X10,X8)
        | ~ r1_orders_2(sK0,X10,X9)
        | ~ r1_orders_2(sK0,sK7(sK0,X8,X9,X10),X10)
        | k11_lattice3(sK0,X8,X9) = X10 )
    | ~ spl9_4 ),
    inference(resolution,[],[f86,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f166,plain,
    ( sK1 != k11_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | spl9_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f2755,plain,
    ( k10_lattice3(sK0,sK1,sK2) != sK5(sK0,sK2,sK1)
    | m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2754,plain,
    ( spl9_46
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_9
    | ~ spl9_37 ),
    inference(avatar_split_clause,[],[f2682,f1981,f134,f123,f118,f89,f79,f74,f2751])).

fof(f1981,plain,
    ( spl9_37
  <=> m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f2682,plain,
    ( k10_lattice3(sK0,sK1,sK2) = sK5(sK0,sK2,sK1)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_9
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f2681,f120])).

fof(f2681,plain,
    ( k10_lattice3(sK0,sK1,sK2) = sK5(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_7
    | spl9_9
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f2658,f125])).

fof(f2658,plain,
    ( k10_lattice3(sK0,sK1,sK2) = sK5(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9
    | ~ spl9_37 ),
    inference(resolution,[],[f1589,f1982])).

fof(f1982,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f1981])).

fof(f1589,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f1588,f140])).

fof(f140,plain,
    ( ! [X6,X5] :
        ( r1_orders_2(sK0,X6,sK5(sK0,X5,X6))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f102,f91])).

fof(f102,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_orders_2(sK0,X6,sK5(sK0,X5,X6))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_3 ),
    inference(resolution,[],[f81,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r1_orders_2(X0,X2,X4)
                            & r1_orders_2(X0,X1,X4) )
                         => r1_orders_2(X0,X3,X4) ) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_lattice3)).

fof(f1588,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X2,X3)) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f1585,f139])).

fof(f139,plain,
    ( ! [X4,X3] :
        ( r1_orders_2(sK0,X3,sK5(sK0,X3,X4))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f101,f91])).

fof(f101,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,sK5(sK0,X3,X4))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_3 ),
    inference(resolution,[],[f81,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,sK5(X0,X1,X2))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1585,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X2,sK5(sK0,X2,X3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X2,X3)) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f1578])).

fof(f1578,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X2,sK5(sK0,X2,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X2,X3))
        | ~ r1_orders_2(sK0,X2,sK5(sK0,X2,X3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f1053,f169])).

fof(f169,plain,
    ( ! [X6,X7,X5] :
        ( r1_orders_2(sK0,X6,sK8(sK0,X5,X6,X7))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,X7)
        | ~ r1_orders_2(sK0,X6,X7)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k10_lattice3(sK0,X5,X6) = X7 )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f168,f91])).

fof(f168,plain,
    ( ! [X6,X7,X5] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,X7)
        | ~ r1_orders_2(sK0,X6,X7)
        | r1_orders_2(sK0,X6,sK8(sK0,X5,X6,X7))
        | k10_lattice3(sK0,X5,X6) = X7 )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f98,f81])).

fof(f98,plain,
    ( ! [X6,X7,X5] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,X7)
        | ~ r1_orders_2(sK0,X6,X7)
        | r1_orders_2(sK0,X6,sK8(sK0,X5,X6,X7))
        | k10_lattice3(sK0,X5,X6) = X7 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f95,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f95,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,X7)
        | ~ r1_orders_2(sK0,X6,X7)
        | r1_orders_2(sK0,X6,sK8(sK0,X5,X6,X7))
        | k10_lattice3(sK0,X5,X6) = X7 )
    | ~ spl9_2 ),
    inference(resolution,[],[f76,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X2,sK8(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).

fof(f1053,plain,
    ( ! [X4,X2,X3] :
        ( ~ r1_orders_2(sK0,X2,sK8(sK0,X3,X4,sK5(sK0,X2,X3)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X4) = sK5(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X4,sK5(sK0,X2,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f1052,f81])).

fof(f1052,plain,
    ( ! [X4,X2,X3] :
        ( k10_lattice3(sK0,X3,X4) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,X3,X4,sK5(sK0,X2,X3)))
        | ~ r1_orders_2(sK0,X4,sK5(sK0,X2,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ v1_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f1041,f91])).

fof(f1041,plain,
    ( ! [X4,X2,X3] :
        ( k10_lattice3(sK0,X3,X4) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,X3,X4,sK5(sK0,X2,X3)))
        | ~ r1_orders_2(sK0,X4,sK5(sK0,X2,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f1036])).

fof(f1036,plain,
    ( ! [X4,X2,X3] :
        ( k10_lattice3(sK0,X3,X4) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,X3,X4,sK5(sK0,X2,X3)))
        | ~ r1_orders_2(sK0,X4,sK5(sK0,X2,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f751,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f751,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0))
        | sK5(sK0,X1,X0) = k10_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK8(sK0,X0,X2,sK5(sK0,X1,X0)))
        | ~ r1_orders_2(sK0,X2,sK5(sK0,X1,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f750,f140])).

fof(f750,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X0) = k10_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK8(sK0,X0,X2,sK5(sK0,X1,X0)))
        | ~ r1_orders_2(sK0,X2,sK5(sK0,X1,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X0))
        | ~ m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0)) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f744])).

fof(f744,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X0) = k10_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK8(sK0,X0,X2,sK5(sK0,X1,X0)))
        | ~ r1_orders_2(sK0,X2,sK5(sK0,X1,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X0))
        | ~ r1_orders_2(sK0,X2,sK5(sK0,X1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X0) = k10_lattice3(sK0,X0,X2) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f504,f158])).

fof(f158,plain,
    ( ! [X4,X2,X3] :
        ( r1_orders_2(sK0,X2,sK8(sK0,X2,X3,X4))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X4)
        | ~ r1_orders_2(sK0,X3,X4)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k10_lattice3(sK0,X2,X3) = X4 )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f157,f91])).

fof(f157,plain,
    ( ! [X4,X2,X3] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X4)
        | ~ r1_orders_2(sK0,X3,X4)
        | r1_orders_2(sK0,X2,sK8(sK0,X2,X3,X4))
        | k10_lattice3(sK0,X2,X3) = X4 )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f97,f81])).

fof(f97,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X4)
        | ~ r1_orders_2(sK0,X3,X4)
        | r1_orders_2(sK0,X2,sK8(sK0,X2,X3,X4))
        | k10_lattice3(sK0,X2,X3) = X4 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f94,f34])).

fof(f94,plain,
    ( ! [X4,X2,X3] :
        ( v2_struct_0(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X4)
        | ~ r1_orders_2(sK0,X3,X4)
        | r1_orders_2(sK0,X2,sK8(sK0,X2,X3,X4))
        | k10_lattice3(sK0,X2,X3) = X4 )
    | ~ spl9_2 ),
    inference(resolution,[],[f76,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,sK8(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f504,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X2,sK8(sK0,X3,X0,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X3,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK8(sK0,X3,X0,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f503,f81])).

fof(f503,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X3,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK8(sK0,X3,X0,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,X3,X0,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ v1_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f502,f91])).

fof(f502,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X3,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK8(sK0,X3,X0,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,X3,X0,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f501])).

fof(f501,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X3,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK8(sK0,X3,X0,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,X3,X0,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f368,f40])).

fof(f368,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK8(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f367,f136])).

fof(f367,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK8(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f366,f91])).

fof(f366,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK8(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f365,f81])).

fof(f365,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK8(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f364,f76])).

fof(f364,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK8(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f363])).

fof(f363,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK8(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | v2_struct_0(sK0)
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(resolution,[],[f271,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | v2_struct_0(X0)
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f271,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK8(sK0,X1,X0,sK5(sK0,X2,X3)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X2,X3))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X2,X3))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X0) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,X1,X0,sK5(sK0,X2,X3)))
        | ~ r1_orders_2(sK0,X3,sK8(sK0,X1,X0,sK5(sK0,X2,X3)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f270,f81])).

fof(f270,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X2,X3))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X2,X3))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X0) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,X1,X0,sK5(sK0,X2,X3)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,X1,X0,sK5(sK0,X2,X3)))
        | ~ r1_orders_2(sK0,X3,sK8(sK0,X1,X0,sK5(sK0,X2,X3)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v1_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f269,f91])).

fof(f269,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X2,X3))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X2,X3))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X0) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,X1,X0,sK5(sK0,X2,X3)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,X1,X0,sK5(sK0,X2,X3)))
        | ~ r1_orders_2(sK0,X3,sK8(sK0,X1,X0,sK5(sK0,X2,X3)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f268])).

fof(f268,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X2,X3))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X2,X3))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X0) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,X1,X0,sK5(sK0,X2,X3)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,X1,X0,sK5(sK0,X2,X3)))
        | ~ r1_orders_2(sK0,X3,sK8(sK0,X1,X0,sK5(sK0,X2,X3)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(resolution,[],[f185,f40])).

fof(f185,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ m1_subset_1(sK5(sK0,X5,X6),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X7,sK5(sK0,X5,X6))
        | ~ r1_orders_2(sK0,X4,sK5(sK0,X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | sK5(sK0,X5,X6) = k10_lattice3(sK0,X7,X4)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,X7,X4,sK5(sK0,X5,X6)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,sK8(sK0,X7,X4,sK5(sK0,X5,X6)))
        | ~ r1_orders_2(sK0,X6,sK8(sK0,X7,X4,sK5(sK0,X5,X6)))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(resolution,[],[f177,f149])).

fof(f149,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f100,f91])).

fof(f100,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2)
        | r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_3 ),
    inference(resolution,[],[f81,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X4)
      | ~ r1_orders_2(X0,X2,X4)
      | r1_orders_2(X0,sK5(X0,X1,X2),X4)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f177,plain,
    ( ! [X10,X8,X9] :
        ( ~ r1_orders_2(sK0,X10,sK8(sK0,X8,X9,X10))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X8,X10)
        | ~ r1_orders_2(sK0,X9,X10)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | k10_lattice3(sK0,X8,X9) = X10 )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f176,f91])).

fof(f176,plain,
    ( ! [X10,X8,X9] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X8,X10)
        | ~ r1_orders_2(sK0,X9,X10)
        | ~ r1_orders_2(sK0,X10,sK8(sK0,X8,X9,X10))
        | k10_lattice3(sK0,X8,X9) = X10 )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f99,f81])).

fof(f99,plain,
    ( ! [X10,X8,X9] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X8,X10)
        | ~ r1_orders_2(sK0,X9,X10)
        | ~ r1_orders_2(sK0,X10,sK8(sK0,X8,X9,X10))
        | k10_lattice3(sK0,X8,X9) = X10 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f96,f34])).

fof(f96,plain,
    ( ! [X10,X8,X9] :
        ( v2_struct_0(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X8,X10)
        | ~ r1_orders_2(sK0,X9,X10)
        | ~ r1_orders_2(sK0,X10,sK8(sK0,X8,X9,X10))
        | k10_lattice3(sK0,X8,X9) = X10 )
    | ~ spl9_2 ),
    inference(resolution,[],[f76,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X3,sK8(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2010,plain,
    ( ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_37 ),
    inference(avatar_contradiction_clause,[],[f2009])).

fof(f2009,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_37 ),
    inference(subsumption_resolution,[],[f2008,f81])).

fof(f2008,plain,
    ( ~ v1_lattice3(sK0)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_37 ),
    inference(subsumption_resolution,[],[f2007,f91])).

fof(f2007,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ spl9_6
    | ~ spl9_7
    | spl9_37 ),
    inference(subsumption_resolution,[],[f2006,f125])).

fof(f2006,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ spl9_6
    | spl9_37 ),
    inference(subsumption_resolution,[],[f2005,f120])).

fof(f2005,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | spl9_37 ),
    inference(resolution,[],[f1983,f40])).

fof(f1983,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | spl9_37 ),
    inference(avatar_component_clause,[],[f1981])).

fof(f1988,plain,
    ( ~ spl9_37
    | spl9_38
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f1937,f1849,f123,f89,f79,f1985,f1981])).

fof(f1849,plain,
    ( spl9_36
  <=> sK5(sK0,sK2,sK1) = sK5(sK0,sK5(sK0,sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f1937,plain,
    ( r1_orders_2(sK0,sK1,sK5(sK0,sK2,sK1))
    | ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_36 ),
    inference(subsumption_resolution,[],[f1873,f125])).

fof(f1873,plain,
    ( r1_orders_2(sK0,sK1,sK5(sK0,sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_36 ),
    inference(superposition,[],[f140,f1851])).

fof(f1851,plain,
    ( sK5(sK0,sK2,sK1) = sK5(sK0,sK5(sK0,sK2,sK1),sK1)
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f1849])).

fof(f1852,plain,
    ( spl9_36
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_9 ),
    inference(avatar_split_clause,[],[f1809,f134,f123,f118,f89,f84,f79,f74,f69,f1849])).

fof(f1809,plain,
    ( sK5(sK0,sK2,sK1) = sK5(sK0,sK5(sK0,sK2,sK1),sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_9 ),
    inference(resolution,[],[f1372,f120])).

fof(f1372,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X1,sK1) = sK5(sK0,sK5(sK0,X1,sK1),sK1) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_9 ),
    inference(resolution,[],[f1369,f125])).

fof(f1369,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X3,X2) = sK5(sK0,sK5(sK0,X3,X2),X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f1359])).

fof(f1359,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X3,X2) = sK5(sK0,sK5(sK0,X3,X2),X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f909,f140])).

fof(f909,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_orders_2(sK0,X8,sK5(sK0,X6,X7))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | sK5(sK0,X6,X7) = sK5(sK0,sK5(sK0,X6,X7),X8)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f908,f81])).

fof(f908,plain,
    ( ! [X6,X8,X7] :
        ( sK5(sK0,X6,X7) = sK5(sK0,sK5(sK0,X6,X7),X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X8,sK5(sK0,X6,X7))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v1_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f900,f91])).

fof(f900,plain,
    ( ! [X6,X8,X7] :
        ( sK5(sK0,X6,X7) = sK5(sK0,sK5(sK0,X6,X7),X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X8,sK5(sK0,X6,X7))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f570,f40])).

fof(f570,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f569,f138])).

fof(f569,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X0)
        | ~ r1_orders_2(sK0,X1,X0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f561])).

fof(f561,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X0)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f410,f139])).

fof(f410,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X2,sK5(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = X2
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f403])).

fof(f403,plain,
    ( ! [X2,X0,X1] :
        ( sK5(sK0,X0,X1) = X2
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK5(sK0,X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f304,f149])).

fof(f304,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X4,X5),X6)
        | sK5(sK0,X4,X5) = X6
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X6,sK5(sK0,X4,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f303,f81])).

fof(f303,plain,
    ( ! [X6,X4,X5] :
        ( sK5(sK0,X4,X5) = X6
        | ~ r1_orders_2(sK0,sK5(sK0,X4,X5),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X6,sK5(sK0,X4,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ v1_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f299,f91])).

fof(f299,plain,
    ( ! [X6,X4,X5] :
        ( sK5(sK0,X4,X5) = X6
        | ~ r1_orders_2(sK0,sK5(sK0,X4,X5),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X6,sK5(sK0,X4,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f266,f40])).

fof(f266,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | X0 = X1
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,
    ( ! [X0,X1] :
        ( X0 = X1
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(superposition,[],[f221,f222])).

fof(f222,plain,
    ( ! [X2,X3] :
        ( k11_lattice3(sK0,X3,X2) = X2
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f219,f138])).

fof(f219,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X2,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k11_lattice3(sK0,X3,X2) = X2 )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X2,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k11_lattice3(sK0,X3,X2) = X2
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X2,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k11_lattice3(sK0,X3,X2) = X2 )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f200,f198])).

fof(f198,plain,
    ( ! [X6,X7,X5] :
        ( r1_orders_2(sK0,sK7(sK0,X5,X6,X7),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X7,X5)
        | ~ r1_orders_2(sK0,X7,X6)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k11_lattice3(sK0,X5,X6) = X7 )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f197,f91])).

fof(f197,plain,
    ( ! [X6,X7,X5] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X7,X5)
        | ~ r1_orders_2(sK0,X7,X6)
        | r1_orders_2(sK0,sK7(sK0,X5,X6,X7),X6)
        | k11_lattice3(sK0,X5,X6) = X7 )
    | ~ spl9_2
    | ~ spl9_4
    | spl9_9 ),
    inference(subsumption_resolution,[],[f110,f136])).

fof(f110,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X7,X5)
        | ~ r1_orders_2(sK0,X7,X6)
        | r1_orders_2(sK0,sK7(sK0,X5,X6,X7),X6)
        | k11_lattice3(sK0,X5,X6) = X7 )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f106,f76])).

fof(f106,plain,
    ( ! [X6,X7,X5] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X7,X5)
        | ~ r1_orders_2(sK0,X7,X6)
        | r1_orders_2(sK0,sK7(sK0,X5,X6,X7),X6)
        | k11_lattice3(sK0,X5,X6) = X7 )
    | ~ spl9_4 ),
    inference(resolution,[],[f86,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f182,plain,
    ( ~ spl9_13
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_11 ),
    inference(avatar_split_clause,[],[f172,f160,f123,f118,f89,f79,f74,f179])).

fof(f179,plain,
    ( spl9_13
  <=> m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f172,plain,
    ( ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_11 ),
    inference(subsumption_resolution,[],[f171,f125])).

fof(f171,plain,
    ( ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6
    | spl9_11 ),
    inference(subsumption_resolution,[],[f170,f120])).

fof(f170,plain,
    ( ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_11 ),
    inference(superposition,[],[f162,f145])).

fof(f162,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl9_11 ),
    inference(avatar_component_clause,[],[f160])).

fof(f167,plain,
    ( ~ spl9_11
    | ~ spl9_12
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_8 ),
    inference(avatar_split_clause,[],[f143,f129,f123,f89,f84,f74,f164,f160])).

fof(f129,plain,
    ( spl9_8
  <=> sK1 = k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f143,plain,
    ( sK1 != k11_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_8 ),
    inference(subsumption_resolution,[],[f142,f125])).

fof(f142,plain,
    ( sK1 != k11_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_8 ),
    inference(superposition,[],[f131,f141])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( k11_lattice3(sK0,X0,X1) = k12_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f108,f91])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = k12_lattice3(sK0,X0,X1) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f104,f76])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = k12_lattice3(sK0,X0,X1) )
    | ~ spl9_4 ),
    inference(resolution,[],[f86,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f131,plain,
    ( sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | spl9_8 ),
    inference(avatar_component_clause,[],[f129])).

fof(f137,plain,
    ( ~ spl9_9
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f127,f89,f79,f134])).

fof(f127,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f103,f91])).

fof(f103,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_struct_0(sK0)
    | ~ spl9_3 ),
    inference(resolution,[],[f81,f34])).

fof(f132,plain,(
    ~ spl9_8 ),
    inference(avatar_split_clause,[],[f27,f129])).

fof(f27,plain,(
    sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_lattice3)).

fof(f126,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f28,f123])).

fof(f28,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f121,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f26,f118])).

fof(f26,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f92,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f33,f89])).

fof(f33,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f87,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f32,f84])).

fof(f32,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f82,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f31,f79])).

fof(f31,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f77,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f30,f74])).

fof(f30,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f72,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f29,f69])).

fof(f29,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:53:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (31587)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (31595)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (31588)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (31601)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (31601)Refutation not found, incomplete strategy% (31601)------------------------------
% 0.21/0.49  % (31601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31601)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (31601)Memory used [KB]: 10618
% 0.21/0.49  % (31601)Time elapsed: 0.070 s
% 0.21/0.49  % (31601)------------------------------
% 0.21/0.49  % (31601)------------------------------
% 0.21/0.49  % (31594)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (31586)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (31589)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (31596)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (31585)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (31591)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (31582)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (31583)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (31584)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (31598)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (31582)Refutation not found, incomplete strategy% (31582)------------------------------
% 0.21/0.51  % (31582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31582)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31582)Memory used [KB]: 10618
% 0.21/0.51  % (31582)Time elapsed: 0.088 s
% 0.21/0.51  % (31582)------------------------------
% 0.21/0.51  % (31582)------------------------------
% 0.21/0.51  % (31599)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (31590)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (31581)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (31592)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (31593)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (31600)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % (31597)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 3.20/0.77  % (31584)Refutation found. Thanks to Tanya!
% 3.20/0.77  % SZS status Theorem for theBenchmark
% 3.20/0.78  % SZS output start Proof for theBenchmark
% 3.20/0.78  fof(f3011,plain,(
% 3.20/0.78    $false),
% 3.20/0.78    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f92,f121,f126,f132,f137,f167,f182,f1852,f1988,f2010,f2754,f2755,f2963,f3009,f3010])).
% 3.20/0.78  fof(f3010,plain,(
% 3.20/0.78    ~spl9_54 | ~spl9_2 | ~spl9_3 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_50),
% 3.20/0.78    inference(avatar_split_clause,[],[f2969,f2960,f123,f118,f89,f79,f74,f3006])).
% 3.20/0.78  fof(f3006,plain,(
% 3.20/0.78    spl9_54 <=> r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).
% 3.20/0.78  fof(f74,plain,(
% 3.20/0.78    spl9_2 <=> v5_orders_2(sK0)),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 3.20/0.78  fof(f79,plain,(
% 3.20/0.78    spl9_3 <=> v1_lattice3(sK0)),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 3.20/0.78  fof(f89,plain,(
% 3.20/0.78    spl9_5 <=> l1_orders_2(sK0)),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 3.20/0.78  fof(f118,plain,(
% 3.20/0.78    spl9_6 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 3.20/0.78  fof(f123,plain,(
% 3.20/0.78    spl9_7 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 3.20/0.78  fof(f2960,plain,(
% 3.20/0.78    spl9_50 <=> r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2))),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).
% 3.20/0.78  fof(f2969,plain,(
% 3.20/0.78    ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | (~spl9_2 | ~spl9_3 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_50)),
% 3.20/0.78    inference(subsumption_resolution,[],[f2968,f125])).
% 3.20/0.78  fof(f125,plain,(
% 3.20/0.78    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl9_7),
% 3.20/0.78    inference(avatar_component_clause,[],[f123])).
% 3.20/0.78  fof(f2968,plain,(
% 3.20/0.78    ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl9_2 | ~spl9_3 | ~spl9_5 | ~spl9_6 | spl9_50)),
% 3.20/0.78    inference(subsumption_resolution,[],[f2967,f120])).
% 3.20/0.78  fof(f120,plain,(
% 3.20/0.78    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl9_6),
% 3.20/0.78    inference(avatar_component_clause,[],[f118])).
% 3.20/0.78  fof(f2967,plain,(
% 3.20/0.78    ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_50)),
% 3.20/0.78    inference(superposition,[],[f2962,f145])).
% 3.20/0.78  fof(f145,plain,(
% 3.20/0.78    ( ! [X0,X1] : (k10_lattice3(sK0,X0,X1) = k13_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(subsumption_resolution,[],[f144,f91])).
% 3.20/0.78  fof(f91,plain,(
% 3.20/0.78    l1_orders_2(sK0) | ~spl9_5),
% 3.20/0.78    inference(avatar_component_clause,[],[f89])).
% 3.20/0.78  fof(f144,plain,(
% 3.20/0.78    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X0,X1) = k13_lattice3(sK0,X0,X1)) ) | (~spl9_2 | ~spl9_3)),
% 3.20/0.78    inference(subsumption_resolution,[],[f93,f81])).
% 3.20/0.78  fof(f81,plain,(
% 3.20/0.78    v1_lattice3(sK0) | ~spl9_3),
% 3.20/0.78    inference(avatar_component_clause,[],[f79])).
% 3.20/0.78  fof(f93,plain,(
% 3.20/0.78    ( ! [X0,X1] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X0,X1) = k13_lattice3(sK0,X0,X1)) ) | ~spl9_2),
% 3.20/0.78    inference(resolution,[],[f76,f61])).
% 3.20/0.78  fof(f61,plain,(
% 3.20/0.78    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)) )),
% 3.20/0.78    inference(cnf_transformation,[],[f25])).
% 3.20/0.78  fof(f25,plain,(
% 3.20/0.78    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 3.20/0.78    inference(flattening,[],[f24])).
% 3.20/0.78  fof(f24,plain,(
% 3.20/0.78    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.20/0.78    inference(ennf_transformation,[],[f7])).
% 3.20/0.78  fof(f7,axiom,(
% 3.20/0.78    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 3.20/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 3.20/0.78  fof(f76,plain,(
% 3.20/0.78    v5_orders_2(sK0) | ~spl9_2),
% 3.20/0.78    inference(avatar_component_clause,[],[f74])).
% 3.20/0.78  fof(f2962,plain,(
% 3.20/0.78    ~r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) | spl9_50),
% 3.20/0.78    inference(avatar_component_clause,[],[f2960])).
% 3.20/0.78  fof(f3009,plain,(
% 3.20/0.78    spl9_54 | ~spl9_38 | ~spl9_46),
% 3.20/0.78    inference(avatar_split_clause,[],[f2822,f2751,f1985,f3006])).
% 3.20/0.78  fof(f1985,plain,(
% 3.20/0.78    spl9_38 <=> r1_orders_2(sK0,sK1,sK5(sK0,sK2,sK1))),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 3.20/0.78  fof(f2751,plain,(
% 3.20/0.78    spl9_46 <=> k10_lattice3(sK0,sK1,sK2) = sK5(sK0,sK2,sK1)),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).
% 3.20/0.78  fof(f2822,plain,(
% 3.20/0.78    r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | (~spl9_38 | ~spl9_46)),
% 3.20/0.78    inference(superposition,[],[f1987,f2753])).
% 3.20/0.78  fof(f2753,plain,(
% 3.20/0.78    k10_lattice3(sK0,sK1,sK2) = sK5(sK0,sK2,sK1) | ~spl9_46),
% 3.20/0.78    inference(avatar_component_clause,[],[f2751])).
% 3.20/0.78  fof(f1987,plain,(
% 3.20/0.78    r1_orders_2(sK0,sK1,sK5(sK0,sK2,sK1)) | ~spl9_38),
% 3.20/0.78    inference(avatar_component_clause,[],[f1985])).
% 3.20/0.78  fof(f2963,plain,(
% 3.20/0.78    ~spl9_50 | ~spl9_1 | ~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_9 | ~spl9_11 | spl9_12),
% 3.20/0.78    inference(avatar_split_clause,[],[f2819,f164,f160,f134,f123,f89,f84,f74,f69,f2960])).
% 3.20/0.78  fof(f69,plain,(
% 3.20/0.78    spl9_1 <=> v3_orders_2(sK0)),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 3.20/0.78  fof(f84,plain,(
% 3.20/0.78    spl9_4 <=> v2_lattice3(sK0)),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 3.20/0.78  fof(f134,plain,(
% 3.20/0.78    spl9_9 <=> v2_struct_0(sK0)),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 3.20/0.78  fof(f160,plain,(
% 3.20/0.78    spl9_11 <=> m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 3.20/0.78  fof(f164,plain,(
% 3.20/0.78    spl9_12 <=> sK1 = k11_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 3.20/0.78  fof(f2819,plain,(
% 3.20/0.78    ~r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) | (~spl9_1 | ~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_9 | ~spl9_11 | spl9_12)),
% 3.20/0.78    inference(subsumption_resolution,[],[f2769,f161])).
% 3.20/0.78  fof(f161,plain,(
% 3.20/0.78    m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~spl9_11),
% 3.20/0.78    inference(avatar_component_clause,[],[f160])).
% 3.20/0.78  fof(f2769,plain,(
% 3.20/0.78    ~r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl9_1 | ~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_9 | spl9_12)),
% 3.20/0.78    inference(subsumption_resolution,[],[f255,f125])).
% 3.20/0.78  fof(f255,plain,(
% 3.20/0.78    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl9_1 | ~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9 | spl9_12)),
% 3.20/0.78    inference(trivial_inequality_removal,[],[f246])).
% 3.20/0.78  fof(f246,plain,(
% 3.20/0.78    sK1 != sK1 | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl9_1 | ~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9 | spl9_12)),
% 3.20/0.78    inference(superposition,[],[f166,f221])).
% 3.20/0.78  fof(f221,plain,(
% 3.20/0.78    ( ! [X0,X1] : (k11_lattice3(sK0,X1,X0) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f220,f138])).
% 3.20/0.78  fof(f138,plain,(
% 3.20/0.78    ( ! [X0] : (r1_orders_2(sK0,X0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f116,f136])).
% 3.20/0.78  fof(f136,plain,(
% 3.20/0.78    ~v2_struct_0(sK0) | spl9_9),
% 3.20/0.78    inference(avatar_component_clause,[],[f134])).
% 3.20/0.78  fof(f116,plain,(
% 3.20/0.78    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0)) ) | (~spl9_1 | ~spl9_5)),
% 3.20/0.78    inference(subsumption_resolution,[],[f112,f71])).
% 3.20/0.78  fof(f71,plain,(
% 3.20/0.78    v3_orders_2(sK0) | ~spl9_1),
% 3.20/0.78    inference(avatar_component_clause,[],[f69])).
% 3.20/0.78  fof(f112,plain,(
% 3.20/0.78    ( ! [X0] : (~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0)) ) | ~spl9_5),
% 3.20/0.78    inference(resolution,[],[f91,f45])).
% 3.20/0.78  fof(f45,plain,(
% 3.20/0.78    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1)) )),
% 3.20/0.78    inference(cnf_transformation,[],[f17])).
% 3.20/0.78  fof(f17,plain,(
% 3.20/0.78    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.20/0.78    inference(flattening,[],[f16])).
% 3.20/0.78  fof(f16,plain,(
% 3.20/0.78    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.20/0.78    inference(ennf_transformation,[],[f1])).
% 3.20/0.78  fof(f1,axiom,(
% 3.20/0.78    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 3.20/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 3.20/0.78  fof(f220,plain,(
% 3.20/0.78    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X1) | ~r1_orders_2(sK0,X1,X0) | k11_lattice3(sK0,X1,X0) = X1) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(duplicate_literal_removal,[],[f217])).
% 3.20/0.78  fof(f217,plain,(
% 3.20/0.78    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X1) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k11_lattice3(sK0,X1,X0) = X1 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X1) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k11_lattice3(sK0,X1,X0) = X1) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(resolution,[],[f200,f191])).
% 3.20/0.78  fof(f191,plain,(
% 3.20/0.78    ( ! [X4,X2,X3] : (r1_orders_2(sK0,sK7(sK0,X2,X3,X4),X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X4,X2) | ~r1_orders_2(sK0,X4,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k11_lattice3(sK0,X2,X3) = X4) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f190,f91])).
% 3.20/0.78  fof(f190,plain,(
% 3.20/0.78    ( ! [X4,X2,X3] : (~l1_orders_2(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X4,X2) | ~r1_orders_2(sK0,X4,X3) | r1_orders_2(sK0,sK7(sK0,X2,X3,X4),X2) | k11_lattice3(sK0,X2,X3) = X4) ) | (~spl9_2 | ~spl9_4 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f109,f136])).
% 3.20/0.78  fof(f109,plain,(
% 3.20/0.78    ( ! [X4,X2,X3] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X4,X2) | ~r1_orders_2(sK0,X4,X3) | r1_orders_2(sK0,sK7(sK0,X2,X3,X4),X2) | k11_lattice3(sK0,X2,X3) = X4) ) | (~spl9_2 | ~spl9_4)),
% 3.20/0.78    inference(subsumption_resolution,[],[f105,f76])).
% 3.20/0.78  fof(f105,plain,(
% 3.20/0.78    ( ! [X4,X2,X3] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X4,X2) | ~r1_orders_2(sK0,X4,X3) | r1_orders_2(sK0,sK7(sK0,X2,X3,X4),X2) | k11_lattice3(sK0,X2,X3) = X4) ) | ~spl9_4),
% 3.20/0.78    inference(resolution,[],[f86,f47])).
% 3.20/0.78  fof(f47,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK7(X0,X1,X2,X3),X1) | k11_lattice3(X0,X1,X2) = X3) )),
% 3.20/0.78    inference(cnf_transformation,[],[f19])).
% 3.20/0.78  fof(f19,plain,(
% 3.20/0.78    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.20/0.78    inference(flattening,[],[f18])).
% 3.20/0.78  fof(f18,plain,(
% 3.20/0.78    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.20/0.78    inference(ennf_transformation,[],[f5])).
% 3.20/0.78  fof(f5,axiom,(
% 3.20/0.78    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 3.20/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).
% 3.20/0.78  fof(f86,plain,(
% 3.20/0.78    v2_lattice3(sK0) | ~spl9_4),
% 3.20/0.78    inference(avatar_component_clause,[],[f84])).
% 3.20/0.78  fof(f200,plain,(
% 3.20/0.78    ( ! [X10,X8,X9] : (~r1_orders_2(sK0,sK7(sK0,X8,X9,X10),X10) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X10,X8) | ~r1_orders_2(sK0,X10,X9) | ~m1_subset_1(X8,u1_struct_0(sK0)) | k11_lattice3(sK0,X8,X9) = X10) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f199,f91])).
% 3.20/0.78  fof(f199,plain,(
% 3.20/0.78    ( ! [X10,X8,X9] : (~l1_orders_2(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X10,X8) | ~r1_orders_2(sK0,X10,X9) | ~r1_orders_2(sK0,sK7(sK0,X8,X9,X10),X10) | k11_lattice3(sK0,X8,X9) = X10) ) | (~spl9_2 | ~spl9_4 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f111,f136])).
% 3.20/0.78  fof(f111,plain,(
% 3.20/0.78    ( ! [X10,X8,X9] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X10,X8) | ~r1_orders_2(sK0,X10,X9) | ~r1_orders_2(sK0,sK7(sK0,X8,X9,X10),X10) | k11_lattice3(sK0,X8,X9) = X10) ) | (~spl9_2 | ~spl9_4)),
% 3.20/0.78    inference(subsumption_resolution,[],[f107,f76])).
% 3.20/0.78  fof(f107,plain,(
% 3.20/0.78    ( ! [X10,X8,X9] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X10,X8) | ~r1_orders_2(sK0,X10,X9) | ~r1_orders_2(sK0,sK7(sK0,X8,X9,X10),X10) | k11_lattice3(sK0,X8,X9) = X10) ) | ~spl9_4),
% 3.20/0.78    inference(resolution,[],[f86,f49])).
% 3.20/0.78  fof(f49,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,sK7(X0,X1,X2,X3),X3) | k11_lattice3(X0,X1,X2) = X3) )),
% 3.20/0.78    inference(cnf_transformation,[],[f19])).
% 3.20/0.78  fof(f166,plain,(
% 3.20/0.78    sK1 != k11_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) | spl9_12),
% 3.20/0.78    inference(avatar_component_clause,[],[f164])).
% 3.20/0.78  fof(f2755,plain,(
% 3.20/0.78    k10_lattice3(sK0,sK1,sK2) != sK5(sK0,sK2,sK1) | m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))),
% 3.20/0.78    introduced(theory_tautology_sat_conflict,[])).
% 3.20/0.78  fof(f2754,plain,(
% 3.20/0.78    spl9_46 | ~spl9_2 | ~spl9_3 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_9 | ~spl9_37),
% 3.20/0.78    inference(avatar_split_clause,[],[f2682,f1981,f134,f123,f118,f89,f79,f74,f2751])).
% 3.20/0.78  fof(f1981,plain,(
% 3.20/0.78    spl9_37 <=> m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 3.20/0.78  fof(f2682,plain,(
% 3.20/0.78    k10_lattice3(sK0,sK1,sK2) = sK5(sK0,sK2,sK1) | (~spl9_2 | ~spl9_3 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_9 | ~spl9_37)),
% 3.20/0.78    inference(subsumption_resolution,[],[f2681,f120])).
% 3.20/0.78  fof(f2681,plain,(
% 3.20/0.78    k10_lattice3(sK0,sK1,sK2) = sK5(sK0,sK2,sK1) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl9_2 | ~spl9_3 | ~spl9_5 | ~spl9_7 | spl9_9 | ~spl9_37)),
% 3.20/0.78    inference(subsumption_resolution,[],[f2658,f125])).
% 3.20/0.78  fof(f2658,plain,(
% 3.20/0.78    k10_lattice3(sK0,sK1,sK2) = sK5(sK0,sK2,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9 | ~spl9_37)),
% 3.20/0.78    inference(resolution,[],[f1589,f1982])).
% 3.20/0.78  fof(f1982,plain,(
% 3.20/0.78    m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0)) | ~spl9_37),
% 3.20/0.78    inference(avatar_component_clause,[],[f1981])).
% 3.20/0.78  fof(f1589,plain,(
% 3.20/0.78    ( ! [X2,X3] : (~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f1588,f140])).
% 3.20/0.78  fof(f140,plain,(
% 3.20/0.78    ( ! [X6,X5] : (r1_orders_2(sK0,X6,sK5(sK0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(subsumption_resolution,[],[f102,f91])).
% 3.20/0.78  fof(f102,plain,(
% 3.20/0.78    ( ! [X6,X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r1_orders_2(sK0,X6,sK5(sK0,X5,X6)) | ~l1_orders_2(sK0)) ) | ~spl9_3),
% 3.20/0.78    inference(resolution,[],[f81,f42])).
% 3.20/0.78  fof(f42,plain,(
% 3.20/0.78    ( ! [X2,X0,X1] : (~v1_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X2,sK5(X0,X1,X2)) | ~l1_orders_2(X0)) )),
% 3.20/0.78    inference(cnf_transformation,[],[f15])).
% 3.20/0.78  fof(f15,plain,(
% 3.20/0.78    ! [X0] : ((v1_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.20/0.78    inference(flattening,[],[f14])).
% 3.20/0.78  fof(f14,plain,(
% 3.20/0.78    ! [X0] : ((v1_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.20/0.78    inference(ennf_transformation,[],[f3])).
% 3.20/0.78  fof(f3,axiom,(
% 3.20/0.78    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))))))),
% 3.20/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_lattice3)).
% 3.20/0.78  fof(f1588,plain,(
% 3.20/0.78    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,sK5(sK0,X2,X3))) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f1585,f139])).
% 3.20/0.78  fof(f139,plain,(
% 3.20/0.78    ( ! [X4,X3] : (r1_orders_2(sK0,X3,sK5(sK0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(subsumption_resolution,[],[f101,f91])).
% 3.20/0.78  fof(f101,plain,(
% 3.20/0.78    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_orders_2(sK0,X3,sK5(sK0,X3,X4)) | ~l1_orders_2(sK0)) ) | ~spl9_3),
% 3.20/0.78    inference(resolution,[],[f81,f41])).
% 3.20/0.78  fof(f41,plain,(
% 3.20/0.78    ( ! [X2,X0,X1] : (~v1_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,sK5(X0,X1,X2)) | ~l1_orders_2(X0)) )),
% 3.20/0.78    inference(cnf_transformation,[],[f15])).
% 3.20/0.78  fof(f1585,plain,(
% 3.20/0.78    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3) | ~r1_orders_2(sK0,X2,sK5(sK0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,sK5(sK0,X2,X3))) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(duplicate_literal_removal,[],[f1578])).
% 3.20/0.78  fof(f1578,plain,(
% 3.20/0.78    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3) | ~r1_orders_2(sK0,X2,sK5(sK0,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,sK5(sK0,X2,X3)) | ~r1_orders_2(sK0,X2,sK5(sK0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(resolution,[],[f1053,f169])).
% 3.20/0.78  fof(f169,plain,(
% 3.20/0.78    ( ! [X6,X7,X5] : (r1_orders_2(sK0,X6,sK8(sK0,X5,X6,X7)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,X7) | ~r1_orders_2(sK0,X6,X7) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k10_lattice3(sK0,X5,X6) = X7) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(subsumption_resolution,[],[f168,f91])).
% 3.20/0.78  fof(f168,plain,(
% 3.20/0.78    ( ! [X6,X7,X5] : (~l1_orders_2(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,X7) | ~r1_orders_2(sK0,X6,X7) | r1_orders_2(sK0,X6,sK8(sK0,X5,X6,X7)) | k10_lattice3(sK0,X5,X6) = X7) ) | (~spl9_2 | ~spl9_3)),
% 3.20/0.78    inference(subsumption_resolution,[],[f98,f81])).
% 3.20/0.78  fof(f98,plain,(
% 3.20/0.78    ( ! [X6,X7,X5] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,X7) | ~r1_orders_2(sK0,X6,X7) | r1_orders_2(sK0,X6,sK8(sK0,X5,X6,X7)) | k10_lattice3(sK0,X5,X6) = X7) ) | ~spl9_2),
% 3.20/0.78    inference(subsumption_resolution,[],[f95,f34])).
% 3.20/0.78  fof(f34,plain,(
% 3.20/0.78    ( ! [X0] : (~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v2_struct_0(X0)) )),
% 3.20/0.78    inference(cnf_transformation,[],[f13])).
% 3.20/0.78  fof(f13,plain,(
% 3.20/0.78    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 3.20/0.78    inference(flattening,[],[f12])).
% 3.20/0.78  fof(f12,plain,(
% 3.20/0.78    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 3.20/0.78    inference(ennf_transformation,[],[f2])).
% 3.20/0.78  fof(f2,axiom,(
% 3.20/0.78    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 3.20/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 3.20/0.78  fof(f95,plain,(
% 3.20/0.78    ( ! [X6,X7,X5] : (v2_struct_0(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,X7) | ~r1_orders_2(sK0,X6,X7) | r1_orders_2(sK0,X6,sK8(sK0,X5,X6,X7)) | k10_lattice3(sK0,X5,X6) = X7) ) | ~spl9_2),
% 3.20/0.78    inference(resolution,[],[f76,f55])).
% 3.20/0.78  fof(f55,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X2,sK8(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3) )),
% 3.20/0.78    inference(cnf_transformation,[],[f21])).
% 3.20/0.78  fof(f21,plain,(
% 3.20/0.78    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.20/0.78    inference(flattening,[],[f20])).
% 3.20/0.78  fof(f20,plain,(
% 3.20/0.78    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.20/0.78    inference(ennf_transformation,[],[f4])).
% 3.20/0.78  fof(f4,axiom,(
% 3.20/0.78    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 3.20/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).
% 3.20/0.78  fof(f1053,plain,(
% 3.20/0.78    ( ! [X4,X2,X3] : (~r1_orders_2(sK0,X2,sK8(sK0,X3,X4,sK5(sK0,X2,X3))) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X4) = sK5(sK0,X2,X3) | ~r1_orders_2(sK0,X4,sK5(sK0,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f1052,f81])).
% 3.20/0.78  fof(f1052,plain,(
% 3.20/0.78    ( ! [X4,X2,X3] : (k10_lattice3(sK0,X3,X4) = sK5(sK0,X2,X3) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK8(sK0,X3,X4,sK5(sK0,X2,X3))) | ~r1_orders_2(sK0,X4,sK5(sK0,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~v1_lattice3(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f1041,f91])).
% 3.20/0.78  fof(f1041,plain,(
% 3.20/0.78    ( ! [X4,X2,X3] : (k10_lattice3(sK0,X3,X4) = sK5(sK0,X2,X3) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK8(sK0,X3,X4,sK5(sK0,X2,X3))) | ~r1_orders_2(sK0,X4,sK5(sK0,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(duplicate_literal_removal,[],[f1036])).
% 3.20/0.78  fof(f1036,plain,(
% 3.20/0.78    ( ! [X4,X2,X3] : (k10_lattice3(sK0,X3,X4) = sK5(sK0,X2,X3) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK8(sK0,X3,X4,sK5(sK0,X2,X3))) | ~r1_orders_2(sK0,X4,sK5(sK0,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(resolution,[],[f751,f40])).
% 3.20/0.78  fof(f40,plain,(
% 3.20/0.78    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0)) )),
% 3.20/0.78    inference(cnf_transformation,[],[f15])).
% 3.20/0.78  fof(f751,plain,(
% 3.20/0.78    ( ! [X2,X0,X1] : (~m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0)) | sK5(sK0,X1,X0) = k10_lattice3(sK0,X0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK8(sK0,X0,X2,sK5(sK0,X1,X0))) | ~r1_orders_2(sK0,X2,sK5(sK0,X1,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f750,f140])).
% 3.20/0.78  fof(f750,plain,(
% 3.20/0.78    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X0) = k10_lattice3(sK0,X0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK8(sK0,X0,X2,sK5(sK0,X1,X0))) | ~r1_orders_2(sK0,X2,sK5(sK0,X1,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK5(sK0,X1,X0)) | ~m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0))) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(duplicate_literal_removal,[],[f744])).
% 3.20/0.78  fof(f744,plain,(
% 3.20/0.78    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X0) = k10_lattice3(sK0,X0,X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK8(sK0,X0,X2,sK5(sK0,X1,X0))) | ~r1_orders_2(sK0,X2,sK5(sK0,X1,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK5(sK0,X1,X0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK5(sK0,X1,X0)) | ~r1_orders_2(sK0,X2,sK5(sK0,X1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X0) = k10_lattice3(sK0,X0,X2)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(resolution,[],[f504,f158])).
% 3.20/0.78  fof(f158,plain,(
% 3.20/0.78    ( ! [X4,X2,X3] : (r1_orders_2(sK0,X2,sK8(sK0,X2,X3,X4)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X4) | ~r1_orders_2(sK0,X3,X4) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k10_lattice3(sK0,X2,X3) = X4) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(subsumption_resolution,[],[f157,f91])).
% 3.20/0.78  fof(f157,plain,(
% 3.20/0.78    ( ! [X4,X2,X3] : (~l1_orders_2(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X4) | ~r1_orders_2(sK0,X3,X4) | r1_orders_2(sK0,X2,sK8(sK0,X2,X3,X4)) | k10_lattice3(sK0,X2,X3) = X4) ) | (~spl9_2 | ~spl9_3)),
% 3.20/0.78    inference(subsumption_resolution,[],[f97,f81])).
% 3.20/0.78  fof(f97,plain,(
% 3.20/0.78    ( ! [X4,X2,X3] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X4) | ~r1_orders_2(sK0,X3,X4) | r1_orders_2(sK0,X2,sK8(sK0,X2,X3,X4)) | k10_lattice3(sK0,X2,X3) = X4) ) | ~spl9_2),
% 3.20/0.78    inference(subsumption_resolution,[],[f94,f34])).
% 3.20/0.78  fof(f94,plain,(
% 3.20/0.78    ( ! [X4,X2,X3] : (v2_struct_0(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X4) | ~r1_orders_2(sK0,X3,X4) | r1_orders_2(sK0,X2,sK8(sK0,X2,X3,X4)) | k10_lattice3(sK0,X2,X3) = X4) ) | ~spl9_2),
% 3.20/0.78    inference(resolution,[],[f76,f54])).
% 3.20/0.78  fof(f54,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,sK8(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3) )),
% 3.20/0.78    inference(cnf_transformation,[],[f21])).
% 3.20/0.78  fof(f504,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X2,sK8(sK0,X3,X0,sK5(sK0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X3,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK8(sK0,X3,X0,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2))) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f503,f81])).
% 3.20/0.78  fof(f503,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X3,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK8(sK0,X3,X0,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X2,sK8(sK0,X3,X0,sK5(sK0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~v1_lattice3(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f502,f91])).
% 3.20/0.78  fof(f502,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X3,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK8(sK0,X3,X0,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X2,sK8(sK0,X3,X0,sK5(sK0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(duplicate_literal_removal,[],[f501])).
% 3.20/0.78  fof(f501,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X3,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK8(sK0,X3,X0,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X2,sK8(sK0,X3,X0,sK5(sK0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(resolution,[],[f368,f40])).
% 3.20/0.78  fof(f368,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK8(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X2,sK8(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK5(sK0,X1,X2))) ) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f367,f136])).
% 3.20/0.78  fof(f367,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK8(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X2,sK8(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(subsumption_resolution,[],[f366,f91])).
% 3.20/0.78  fof(f366,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK8(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X2,sK8(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(subsumption_resolution,[],[f365,f81])).
% 3.20/0.78  fof(f365,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK8(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X2,sK8(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(subsumption_resolution,[],[f364,f76])).
% 3.20/0.78  fof(f364,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK8(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X2,sK8(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(duplicate_literal_removal,[],[f363])).
% 3.20/0.78  fof(f363,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK8(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X2,sK8(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | v2_struct_0(sK0) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(resolution,[],[f271,f53])).
% 3.20/0.78  fof(f53,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | v2_struct_0(X0) | k10_lattice3(X0,X1,X2) = X3) )),
% 3.20/0.78    inference(cnf_transformation,[],[f21])).
% 3.20/0.78  fof(f271,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK8(sK0,X1,X0,sK5(sK0,X2,X3)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK5(sK0,X2,X3)) | ~r1_orders_2(sK0,X0,sK5(sK0,X2,X3)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X0) = sK5(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK8(sK0,X1,X0,sK5(sK0,X2,X3))) | ~r1_orders_2(sK0,X3,sK8(sK0,X1,X0,sK5(sK0,X2,X3))) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(subsumption_resolution,[],[f270,f81])).
% 3.20/0.78  fof(f270,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK5(sK0,X2,X3)) | ~r1_orders_2(sK0,X0,sK5(sK0,X2,X3)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X0) = sK5(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK8(sK0,X1,X0,sK5(sK0,X2,X3)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK8(sK0,X1,X0,sK5(sK0,X2,X3))) | ~r1_orders_2(sK0,X3,sK8(sK0,X1,X0,sK5(sK0,X2,X3))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v1_lattice3(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(subsumption_resolution,[],[f269,f91])).
% 3.20/0.78  fof(f269,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK5(sK0,X2,X3)) | ~r1_orders_2(sK0,X0,sK5(sK0,X2,X3)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X0) = sK5(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK8(sK0,X1,X0,sK5(sK0,X2,X3)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK8(sK0,X1,X0,sK5(sK0,X2,X3))) | ~r1_orders_2(sK0,X3,sK8(sK0,X1,X0,sK5(sK0,X2,X3))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(duplicate_literal_removal,[],[f268])).
% 3.20/0.78  fof(f268,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK5(sK0,X2,X3)) | ~r1_orders_2(sK0,X0,sK5(sK0,X2,X3)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X0) = sK5(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK8(sK0,X1,X0,sK5(sK0,X2,X3)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK8(sK0,X1,X0,sK5(sK0,X2,X3))) | ~r1_orders_2(sK0,X3,sK8(sK0,X1,X0,sK5(sK0,X2,X3))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(resolution,[],[f185,f40])).
% 3.20/0.78  fof(f185,plain,(
% 3.20/0.78    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK5(sK0,X5,X6),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X7,sK5(sK0,X5,X6)) | ~r1_orders_2(sK0,X4,sK5(sK0,X5,X6)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | sK5(sK0,X5,X6) = k10_lattice3(sK0,X7,X4) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(sK8(sK0,X7,X4,sK5(sK0,X5,X6)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,sK8(sK0,X7,X4,sK5(sK0,X5,X6))) | ~r1_orders_2(sK0,X6,sK8(sK0,X7,X4,sK5(sK0,X5,X6))) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(resolution,[],[f177,f149])).
% 3.20/0.78  fof(f149,plain,(
% 3.20/0.78    ( ! [X2,X0,X1] : (r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X2) | ~r1_orders_2(sK0,X1,X2) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(subsumption_resolution,[],[f100,f91])).
% 3.20/0.78  fof(f100,plain,(
% 3.20/0.78    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X2) | ~r1_orders_2(sK0,X1,X2) | r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~l1_orders_2(sK0)) ) | ~spl9_3),
% 3.20/0.78    inference(resolution,[],[f81,f39])).
% 3.20/0.78  fof(f39,plain,(
% 3.20/0.78    ( ! [X4,X2,X0,X1] : (~v1_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X4) | ~r1_orders_2(X0,X2,X4) | r1_orders_2(X0,sK5(X0,X1,X2),X4) | ~l1_orders_2(X0)) )),
% 3.20/0.78    inference(cnf_transformation,[],[f15])).
% 3.20/0.78  fof(f177,plain,(
% 3.20/0.78    ( ! [X10,X8,X9] : (~r1_orders_2(sK0,X10,sK8(sK0,X8,X9,X10)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X8,X10) | ~r1_orders_2(sK0,X9,X10) | ~m1_subset_1(X8,u1_struct_0(sK0)) | k10_lattice3(sK0,X8,X9) = X10) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(subsumption_resolution,[],[f176,f91])).
% 3.20/0.78  fof(f176,plain,(
% 3.20/0.78    ( ! [X10,X8,X9] : (~l1_orders_2(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X8,X10) | ~r1_orders_2(sK0,X9,X10) | ~r1_orders_2(sK0,X10,sK8(sK0,X8,X9,X10)) | k10_lattice3(sK0,X8,X9) = X10) ) | (~spl9_2 | ~spl9_3)),
% 3.20/0.78    inference(subsumption_resolution,[],[f99,f81])).
% 3.20/0.78  fof(f99,plain,(
% 3.20/0.78    ( ! [X10,X8,X9] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X8,X10) | ~r1_orders_2(sK0,X9,X10) | ~r1_orders_2(sK0,X10,sK8(sK0,X8,X9,X10)) | k10_lattice3(sK0,X8,X9) = X10) ) | ~spl9_2),
% 3.20/0.78    inference(subsumption_resolution,[],[f96,f34])).
% 3.20/0.78  fof(f96,plain,(
% 3.20/0.78    ( ! [X10,X8,X9] : (v2_struct_0(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X8,X10) | ~r1_orders_2(sK0,X9,X10) | ~r1_orders_2(sK0,X10,sK8(sK0,X8,X9,X10)) | k10_lattice3(sK0,X8,X9) = X10) ) | ~spl9_2),
% 3.20/0.78    inference(resolution,[],[f76,f56])).
% 3.20/0.78  fof(f56,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X3,sK8(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3) )),
% 3.20/0.78    inference(cnf_transformation,[],[f21])).
% 3.20/0.78  fof(f2010,plain,(
% 3.20/0.78    ~spl9_3 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_37),
% 3.20/0.78    inference(avatar_contradiction_clause,[],[f2009])).
% 3.20/0.78  fof(f2009,plain,(
% 3.20/0.78    $false | (~spl9_3 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_37)),
% 3.20/0.78    inference(subsumption_resolution,[],[f2008,f81])).
% 3.20/0.78  fof(f2008,plain,(
% 3.20/0.78    ~v1_lattice3(sK0) | (~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_37)),
% 3.20/0.78    inference(subsumption_resolution,[],[f2007,f91])).
% 3.20/0.78  fof(f2007,plain,(
% 3.20/0.78    ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | (~spl9_6 | ~spl9_7 | spl9_37)),
% 3.20/0.78    inference(subsumption_resolution,[],[f2006,f125])).
% 3.20/0.78  fof(f2006,plain,(
% 3.20/0.78    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | (~spl9_6 | spl9_37)),
% 3.20/0.78    inference(subsumption_resolution,[],[f2005,f120])).
% 3.20/0.78  fof(f2005,plain,(
% 3.20/0.78    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | spl9_37),
% 3.20/0.78    inference(resolution,[],[f1983,f40])).
% 3.20/0.78  fof(f1983,plain,(
% 3.20/0.78    ~m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0)) | spl9_37),
% 3.20/0.78    inference(avatar_component_clause,[],[f1981])).
% 3.20/0.78  fof(f1988,plain,(
% 3.20/0.78    ~spl9_37 | spl9_38 | ~spl9_3 | ~spl9_5 | ~spl9_7 | ~spl9_36),
% 3.20/0.78    inference(avatar_split_clause,[],[f1937,f1849,f123,f89,f79,f1985,f1981])).
% 3.20/0.78  fof(f1849,plain,(
% 3.20/0.78    spl9_36 <=> sK5(sK0,sK2,sK1) = sK5(sK0,sK5(sK0,sK2,sK1),sK1)),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 3.20/0.78  fof(f1937,plain,(
% 3.20/0.78    r1_orders_2(sK0,sK1,sK5(sK0,sK2,sK1)) | ~m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0)) | (~spl9_3 | ~spl9_5 | ~spl9_7 | ~spl9_36)),
% 3.20/0.78    inference(subsumption_resolution,[],[f1873,f125])).
% 3.20/0.78  fof(f1873,plain,(
% 3.20/0.78    r1_orders_2(sK0,sK1,sK5(sK0,sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0)) | (~spl9_3 | ~spl9_5 | ~spl9_36)),
% 3.20/0.78    inference(superposition,[],[f140,f1851])).
% 3.20/0.78  fof(f1851,plain,(
% 3.20/0.78    sK5(sK0,sK2,sK1) = sK5(sK0,sK5(sK0,sK2,sK1),sK1) | ~spl9_36),
% 3.20/0.78    inference(avatar_component_clause,[],[f1849])).
% 3.20/0.78  fof(f1852,plain,(
% 3.20/0.78    spl9_36 | ~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_9),
% 3.20/0.78    inference(avatar_split_clause,[],[f1809,f134,f123,f118,f89,f84,f79,f74,f69,f1849])).
% 3.20/0.78  fof(f1809,plain,(
% 3.20/0.78    sK5(sK0,sK2,sK1) = sK5(sK0,sK5(sK0,sK2,sK1),sK1) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_9)),
% 3.20/0.78    inference(resolution,[],[f1372,f120])).
% 3.20/0.78  fof(f1372,plain,(
% 3.20/0.78    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X1,sK1) = sK5(sK0,sK5(sK0,X1,sK1),sK1)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_9)),
% 3.20/0.78    inference(resolution,[],[f1369,f125])).
% 3.20/0.78  fof(f1369,plain,(
% 3.20/0.78    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X3,X2) = sK5(sK0,sK5(sK0,X3,X2),X2) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(duplicate_literal_removal,[],[f1359])).
% 3.20/0.78  fof(f1359,plain,(
% 3.20/0.78    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X3,X2) = sK5(sK0,sK5(sK0,X3,X2),X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(resolution,[],[f909,f140])).
% 3.20/0.78  fof(f909,plain,(
% 3.20/0.78    ( ! [X6,X8,X7] : (~r1_orders_2(sK0,X8,sK5(sK0,X6,X7)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | sK5(sK0,X6,X7) = sK5(sK0,sK5(sK0,X6,X7),X8) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f908,f81])).
% 3.20/0.78  fof(f908,plain,(
% 3.20/0.78    ( ! [X6,X8,X7] : (sK5(sK0,X6,X7) = sK5(sK0,sK5(sK0,X6,X7),X8) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X8,sK5(sK0,X6,X7)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~v1_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f900,f91])).
% 3.20/0.78  fof(f900,plain,(
% 3.20/0.78    ( ! [X6,X8,X7] : (sK5(sK0,X6,X7) = sK5(sK0,sK5(sK0,X6,X7),X8) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X8,sK5(sK0,X6,X7)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(resolution,[],[f570,f40])).
% 3.20/0.78  fof(f570,plain,(
% 3.20/0.78    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = X0 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f569,f138])).
% 3.20/0.78  fof(f569,plain,(
% 3.20/0.78    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = X0 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X0) | ~r1_orders_2(sK0,X1,X0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(duplicate_literal_removal,[],[f561])).
% 3.20/0.78  fof(f561,plain,(
% 3.20/0.78    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X0) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(resolution,[],[f410,f139])).
% 3.20/0.78  fof(f410,plain,(
% 3.20/0.78    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X2,sK5(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = X2 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X2) | ~r1_orders_2(sK0,X1,X2)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(duplicate_literal_removal,[],[f403])).
% 3.20/0.78  fof(f403,plain,(
% 3.20/0.78    ( ! [X2,X0,X1] : (sK5(sK0,X0,X1) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK5(sK0,X0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X2) | ~r1_orders_2(sK0,X1,X2) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(resolution,[],[f304,f149])).
% 3.20/0.78  fof(f304,plain,(
% 3.20/0.78    ( ! [X6,X4,X5] : (~r1_orders_2(sK0,sK5(sK0,X4,X5),X6) | sK5(sK0,X4,X5) = X6 | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X6,sK5(sK0,X4,X5)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f303,f81])).
% 3.20/0.78  fof(f303,plain,(
% 3.20/0.78    ( ! [X6,X4,X5] : (sK5(sK0,X4,X5) = X6 | ~r1_orders_2(sK0,sK5(sK0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X6,sK5(sK0,X4,X5)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~v1_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f299,f91])).
% 3.20/0.78  fof(f299,plain,(
% 3.20/0.78    ( ! [X6,X4,X5] : (sK5(sK0,X4,X5) = X6 | ~r1_orders_2(sK0,sK5(sK0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X6,sK5(sK0,X4,X5)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(resolution,[],[f266,f40])).
% 3.20/0.78  fof(f266,plain,(
% 3.20/0.78    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | X0 = X1 | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(duplicate_literal_removal,[],[f259])).
% 3.20/0.78  fof(f259,plain,(
% 3.20/0.78    ( ! [X0,X1] : (X0 = X1 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(superposition,[],[f221,f222])).
% 3.20/0.78  fof(f222,plain,(
% 3.20/0.78    ( ! [X2,X3] : (k11_lattice3(sK0,X3,X2) = X2 | ~r1_orders_2(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f219,f138])).
% 3.20/0.78  fof(f219,plain,(
% 3.20/0.78    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X3) | ~r1_orders_2(sK0,X2,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k11_lattice3(sK0,X3,X2) = X2) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(duplicate_literal_removal,[],[f218])).
% 3.20/0.78  fof(f218,plain,(
% 3.20/0.78    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X3) | ~r1_orders_2(sK0,X2,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k11_lattice3(sK0,X3,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X3) | ~r1_orders_2(sK0,X2,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k11_lattice3(sK0,X3,X2) = X2) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(resolution,[],[f200,f198])).
% 3.20/0.78  fof(f198,plain,(
% 3.20/0.78    ( ! [X6,X7,X5] : (r1_orders_2(sK0,sK7(sK0,X5,X6,X7),X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X7,X5) | ~r1_orders_2(sK0,X7,X6) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k11_lattice3(sK0,X5,X6) = X7) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f197,f91])).
% 3.20/0.78  fof(f197,plain,(
% 3.20/0.78    ( ! [X6,X7,X5] : (~l1_orders_2(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X7,X5) | ~r1_orders_2(sK0,X7,X6) | r1_orders_2(sK0,sK7(sK0,X5,X6,X7),X6) | k11_lattice3(sK0,X5,X6) = X7) ) | (~spl9_2 | ~spl9_4 | spl9_9)),
% 3.20/0.78    inference(subsumption_resolution,[],[f110,f136])).
% 3.20/0.78  fof(f110,plain,(
% 3.20/0.78    ( ! [X6,X7,X5] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X7,X5) | ~r1_orders_2(sK0,X7,X6) | r1_orders_2(sK0,sK7(sK0,X5,X6,X7),X6) | k11_lattice3(sK0,X5,X6) = X7) ) | (~spl9_2 | ~spl9_4)),
% 3.20/0.78    inference(subsumption_resolution,[],[f106,f76])).
% 3.20/0.78  fof(f106,plain,(
% 3.20/0.78    ( ! [X6,X7,X5] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X7,X5) | ~r1_orders_2(sK0,X7,X6) | r1_orders_2(sK0,sK7(sK0,X5,X6,X7),X6) | k11_lattice3(sK0,X5,X6) = X7) ) | ~spl9_4),
% 3.20/0.78    inference(resolution,[],[f86,f48])).
% 3.20/0.78  fof(f48,plain,(
% 3.20/0.78    ( ! [X2,X0,X3,X1] : (~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK7(X0,X1,X2,X3),X2) | k11_lattice3(X0,X1,X2) = X3) )),
% 3.20/0.78    inference(cnf_transformation,[],[f19])).
% 3.20/0.78  fof(f182,plain,(
% 3.20/0.78    ~spl9_13 | ~spl9_2 | ~spl9_3 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_11),
% 3.20/0.78    inference(avatar_split_clause,[],[f172,f160,f123,f118,f89,f79,f74,f179])).
% 3.20/0.78  fof(f179,plain,(
% 3.20/0.78    spl9_13 <=> m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 3.20/0.78  fof(f172,plain,(
% 3.20/0.78    ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl9_2 | ~spl9_3 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_11)),
% 3.20/0.78    inference(subsumption_resolution,[],[f171,f125])).
% 3.20/0.78  fof(f171,plain,(
% 3.20/0.78    ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl9_2 | ~spl9_3 | ~spl9_5 | ~spl9_6 | spl9_11)),
% 3.20/0.78    inference(subsumption_resolution,[],[f170,f120])).
% 3.20/0.78  fof(f170,plain,(
% 3.20/0.78    ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_11)),
% 3.20/0.78    inference(superposition,[],[f162,f145])).
% 3.20/0.78  fof(f162,plain,(
% 3.20/0.78    ~m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | spl9_11),
% 3.20/0.78    inference(avatar_component_clause,[],[f160])).
% 3.20/0.78  fof(f167,plain,(
% 3.20/0.78    ~spl9_11 | ~spl9_12 | ~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_8),
% 3.20/0.78    inference(avatar_split_clause,[],[f143,f129,f123,f89,f84,f74,f164,f160])).
% 3.20/0.78  fof(f129,plain,(
% 3.20/0.78    spl9_8 <=> sK1 = k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))),
% 3.20/0.78    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 3.20/0.78  fof(f143,plain,(
% 3.20/0.78    sK1 != k11_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_8)),
% 3.20/0.78    inference(subsumption_resolution,[],[f142,f125])).
% 3.20/0.78  fof(f142,plain,(
% 3.20/0.78    sK1 != k11_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_8)),
% 3.20/0.78    inference(superposition,[],[f131,f141])).
% 3.20/0.78  fof(f141,plain,(
% 3.20/0.78    ( ! [X0,X1] : (k11_lattice3(sK0,X0,X1) = k12_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5)),
% 3.20/0.78    inference(subsumption_resolution,[],[f108,f91])).
% 3.20/0.78  fof(f108,plain,(
% 3.20/0.78    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = k12_lattice3(sK0,X0,X1)) ) | (~spl9_2 | ~spl9_4)),
% 3.20/0.78    inference(subsumption_resolution,[],[f104,f76])).
% 3.20/0.78  fof(f104,plain,(
% 3.20/0.78    ( ! [X0,X1] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = k12_lattice3(sK0,X0,X1)) ) | ~spl9_4),
% 3.20/0.78    inference(resolution,[],[f86,f60])).
% 3.20/0.78  fof(f60,plain,(
% 3.20/0.78    ( ! [X2,X0,X1] : (~v2_lattice3(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)) )),
% 3.20/0.78    inference(cnf_transformation,[],[f23])).
% 3.20/0.78  fof(f23,plain,(
% 3.20/0.78    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.20/0.78    inference(flattening,[],[f22])).
% 3.20/0.78  fof(f22,plain,(
% 3.20/0.78    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.20/0.78    inference(ennf_transformation,[],[f6])).
% 3.20/0.78  fof(f6,axiom,(
% 3.20/0.78    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 3.20/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 3.20/0.78  fof(f131,plain,(
% 3.20/0.78    sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) | spl9_8),
% 3.20/0.78    inference(avatar_component_clause,[],[f129])).
% 3.20/0.78  fof(f137,plain,(
% 3.20/0.78    ~spl9_9 | ~spl9_3 | ~spl9_5),
% 3.20/0.78    inference(avatar_split_clause,[],[f127,f89,f79,f134])).
% 3.20/0.78  fof(f127,plain,(
% 3.20/0.78    ~v2_struct_0(sK0) | (~spl9_3 | ~spl9_5)),
% 3.20/0.78    inference(subsumption_resolution,[],[f103,f91])).
% 3.20/0.78  fof(f103,plain,(
% 3.20/0.78    ~l1_orders_2(sK0) | ~v2_struct_0(sK0) | ~spl9_3),
% 3.20/0.78    inference(resolution,[],[f81,f34])).
% 3.20/0.78  fof(f132,plain,(
% 3.20/0.78    ~spl9_8),
% 3.20/0.78    inference(avatar_split_clause,[],[f27,f129])).
% 3.20/0.78  fof(f27,plain,(
% 3.20/0.78    sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))),
% 3.20/0.78    inference(cnf_transformation,[],[f11])).
% 3.20/0.78  fof(f11,plain,(
% 3.20/0.78    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 3.20/0.78    inference(flattening,[],[f10])).
% 3.20/0.78  fof(f10,plain,(
% 3.20/0.78    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 3.20/0.78    inference(ennf_transformation,[],[f9])).
% 3.20/0.78  fof(f9,negated_conjecture,(
% 3.20/0.78    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 3.20/0.78    inference(negated_conjecture,[],[f8])).
% 3.20/0.78  fof(f8,conjecture,(
% 3.20/0.78    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 3.20/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_lattice3)).
% 3.20/0.78  fof(f126,plain,(
% 3.20/0.78    spl9_7),
% 3.20/0.78    inference(avatar_split_clause,[],[f28,f123])).
% 3.20/0.78  fof(f28,plain,(
% 3.20/0.78    m1_subset_1(sK1,u1_struct_0(sK0))),
% 3.20/0.78    inference(cnf_transformation,[],[f11])).
% 3.20/0.78  fof(f121,plain,(
% 3.20/0.78    spl9_6),
% 3.20/0.78    inference(avatar_split_clause,[],[f26,f118])).
% 3.20/0.78  fof(f26,plain,(
% 3.20/0.78    m1_subset_1(sK2,u1_struct_0(sK0))),
% 3.20/0.78    inference(cnf_transformation,[],[f11])).
% 3.20/0.78  fof(f92,plain,(
% 3.20/0.78    spl9_5),
% 3.20/0.78    inference(avatar_split_clause,[],[f33,f89])).
% 3.20/0.78  fof(f33,plain,(
% 3.20/0.78    l1_orders_2(sK0)),
% 3.20/0.78    inference(cnf_transformation,[],[f11])).
% 3.20/0.78  fof(f87,plain,(
% 3.20/0.78    spl9_4),
% 3.20/0.78    inference(avatar_split_clause,[],[f32,f84])).
% 3.20/0.78  fof(f32,plain,(
% 3.20/0.78    v2_lattice3(sK0)),
% 3.20/0.78    inference(cnf_transformation,[],[f11])).
% 3.20/0.78  fof(f82,plain,(
% 3.20/0.78    spl9_3),
% 3.20/0.78    inference(avatar_split_clause,[],[f31,f79])).
% 3.20/0.78  fof(f31,plain,(
% 3.20/0.78    v1_lattice3(sK0)),
% 3.20/0.78    inference(cnf_transformation,[],[f11])).
% 3.20/0.78  fof(f77,plain,(
% 3.20/0.78    spl9_2),
% 3.20/0.78    inference(avatar_split_clause,[],[f30,f74])).
% 3.20/0.78  fof(f30,plain,(
% 3.20/0.78    v5_orders_2(sK0)),
% 3.20/0.78    inference(cnf_transformation,[],[f11])).
% 3.20/0.78  fof(f72,plain,(
% 3.20/0.78    spl9_1),
% 3.20/0.78    inference(avatar_split_clause,[],[f29,f69])).
% 3.20/0.78  fof(f29,plain,(
% 3.20/0.78    v3_orders_2(sK0)),
% 3.20/0.78    inference(cnf_transformation,[],[f11])).
% 3.20/0.78  % SZS output end Proof for theBenchmark
% 3.20/0.78  % (31584)------------------------------
% 3.20/0.78  % (31584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.78  % (31584)Termination reason: Refutation
% 3.20/0.78  
% 3.20/0.78  % (31584)Memory used [KB]: 13048
% 3.20/0.78  % (31584)Time elapsed: 0.333 s
% 3.20/0.78  % (31584)------------------------------
% 3.20/0.78  % (31584)------------------------------
% 3.20/0.78  % (31580)Success in time 0.417 s
%------------------------------------------------------------------------------
