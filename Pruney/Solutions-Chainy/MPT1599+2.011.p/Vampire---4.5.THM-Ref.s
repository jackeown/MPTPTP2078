%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 646 expanded)
%              Number of leaves         :   30 ( 237 expanded)
%              Depth                    :   19
%              Number of atoms          :  674 (2168 expanded)
%              Number of equality atoms :   71 ( 315 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f704,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f101,f106,f159,f189,f223,f247,f661,f666,f675,f703])).

fof(f703,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | spl3_28 ),
    inference(avatar_contradiction_clause,[],[f702])).

fof(f702,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | spl3_28 ),
    inference(subsumption_resolution,[],[f695,f361])).

fof(f361,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f284,f241])).

fof(f241,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f197,f238])).

fof(f238,plain,
    ( sK2 = k11_lattice3(k2_yellow_1(sK0),sK2,sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f181,f234])).

fof(f234,plain,
    ( sK2 = k12_lattice3(k2_yellow_1(sK0),sK2,sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f93,f93,f83,f222,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 ) ),
    inference(forward_demodulation,[],[f139,f52])).

fof(f52,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 ) ),
    inference(forward_demodulation,[],[f138,f52])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 ) ),
    inference(subsumption_resolution,[],[f137,f47])).

fof(f47,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1
      | ~ v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f136,f51])).

fof(f51,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1
      | ~ v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f58,f49])).

fof(f49,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | k12_lattice3(X0,X1,X2) = X1
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k12_lattice3(X0,X1,X2) = X1
                  | ~ r3_orders_2(X0,X1,X2) )
                & ( r3_orders_2(X0,X1,X2)
                  | k12_lattice3(X0,X1,X2) != X1 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_0)).

fof(f222,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK2,sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl3_10
  <=> r3_orders_2(k2_yellow_1(sK0),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f83,plain,
    ( v2_lattice3(k2_yellow_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_2
  <=> v2_lattice3(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f93,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f181,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK2,sK2) = k12_lattice3(k2_yellow_1(sK0),sK2,sK2)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f93,f93,f83,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,X1)
      | k11_lattice3(k2_yellow_1(X1),X2,X0) = k12_lattice3(k2_yellow_1(X1),X2,X0) ) ),
    inference(forward_demodulation,[],[f129,f52])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ v2_lattice3(k2_yellow_1(X1))
      | k11_lattice3(k2_yellow_1(X1),X2,X0) = k12_lattice3(k2_yellow_1(X1),X2,X0) ) ),
    inference(forward_demodulation,[],[f128,f52])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ v2_lattice3(k2_yellow_1(X1))
      | k11_lattice3(k2_yellow_1(X1),X2,X0) = k12_lattice3(k2_yellow_1(X1),X2,X0) ) ),
    inference(subsumption_resolution,[],[f127,f51])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ l1_orders_2(k2_yellow_1(X1))
      | ~ v2_lattice3(k2_yellow_1(X1))
      | k11_lattice3(k2_yellow_1(X1),X2,X0) = k12_lattice3(k2_yellow_1(X1),X2,X0) ) ),
    inference(resolution,[],[f63,f49])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f197,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f88,f93,f93,f83,f146])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_lattice3(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X0)
      | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3) = k11_lattice3(k2_yellow_1(X0),X1,k11_lattice3(k2_yellow_1(X0),X2,X3))
      | ~ m1_subset_1(X1,X0) ) ),
    inference(forward_demodulation,[],[f145,f52])).

fof(f145,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X0)
      | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3) = k11_lattice3(k2_yellow_1(X0),X1,k11_lattice3(k2_yellow_1(X0),X2,X3))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v2_lattice3(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f144,f52])).

fof(f144,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,X0)
      | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3) = k11_lattice3(k2_yellow_1(X0),X1,k11_lattice3(k2_yellow_1(X0),X2,X3))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v2_lattice3(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f143,f52])).

fof(f143,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3) = k11_lattice3(k2_yellow_1(X0),X1,k11_lattice3(k2_yellow_1(X0),X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v2_lattice3(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f142,f49])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3) = k11_lattice3(k2_yellow_1(X0),X1,k11_lattice3(k2_yellow_1(X0),X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f141,f51])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3) = k11_lattice3(k2_yellow_1(X0),X1,k11_lattice3(k2_yellow_1(X0),X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f60,f48])).

fof(f48,plain,(
    ! [X0] : v4_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3))
                  | ~ v4_orders_2(X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3))
                  | ~ v4_orders_2(X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( v4_orders_2(X0)
                   => k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_lattice3)).

fof(f88,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f284,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f93,f83,f246,f130])).

fof(f246,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl3_11
  <=> m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f695,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_11
    | spl3_28 ),
    inference(unit_resulting_resolution,[],[f83,f93,f246,f665,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | k12_lattice3(k2_yellow_1(X0),X1,X2) != X1
      | ~ m1_subset_1(X1,X0)
      | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f134,f52])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k12_lattice3(k2_yellow_1(X0),X1,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f133,f52])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(k2_yellow_1(X0),X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(subsumption_resolution,[],[f132,f47])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(k2_yellow_1(X0),X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f131,f51])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(k2_yellow_1(X0),X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f57,f49])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | k12_lattice3(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f665,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | spl3_28 ),
    inference(avatar_component_clause,[],[f663])).

fof(f663,plain,
    ( spl3_28
  <=> r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f675,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_11
    | spl3_27 ),
    inference(avatar_contradiction_clause,[],[f674])).

fof(f674,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_11
    | spl3_27 ),
    inference(subsumption_resolution,[],[f667,f362])).

fof(f362,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f283,f233])).

fof(f233,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f204,f232])).

fof(f232,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f229,f174])).

fof(f174,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f88,f93,f83,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,X1)
      | k11_lattice3(k2_yellow_1(X1),X0,X2) = k11_lattice3(k2_yellow_1(X1),X2,X0) ) ),
    inference(forward_demodulation,[],[f125,f52])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ v2_lattice3(k2_yellow_1(X1))
      | k11_lattice3(k2_yellow_1(X1),X0,X2) = k11_lattice3(k2_yellow_1(X1),X2,X0) ) ),
    inference(forward_demodulation,[],[f124,f52])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ v2_lattice3(k2_yellow_1(X1))
      | k11_lattice3(k2_yellow_1(X1),X0,X2) = k11_lattice3(k2_yellow_1(X1),X2,X0) ) ),
    inference(subsumption_resolution,[],[f123,f51])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ l1_orders_2(k2_yellow_1(X1))
      | ~ v2_lattice3(k2_yellow_1(X1))
      | k11_lattice3(k2_yellow_1(X1),X0,X2) = k11_lattice3(k2_yellow_1(X1),X2,X0) ) ),
    inference(resolution,[],[f59,f49])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_lattice3)).

fof(f229,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK2,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f206,f228])).

fof(f228,plain,
    ( sK1 = k11_lattice3(k2_yellow_1(sK0),sK1,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f178,f224])).

fof(f224,plain,
    ( sK1 = k12_lattice3(k2_yellow_1(sK0),sK1,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f88,f88,f83,f188,f140])).

fof(f188,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK1,sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl3_9
  <=> r3_orders_2(k2_yellow_1(sK0),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f178,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK1) = k12_lattice3(k2_yellow_1(sK0),sK1,sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f88,f88,f83,f130])).

fof(f206,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK1)) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f205,f204])).

fof(f205,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK1)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f192,f174])).

fof(f192,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f93,f88,f88,f83,f146])).

fof(f204,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f193,f174])).

fof(f193,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f88,f93,f88,f83,f146])).

fof(f283,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f88,f83,f246,f130])).

fof(f667,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_11
    | spl3_27 ),
    inference(unit_resulting_resolution,[],[f83,f88,f246,f660,f135])).

fof(f660,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | spl3_27 ),
    inference(avatar_component_clause,[],[f658])).

fof(f658,plain,
    ( spl3_27
  <=> r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f666,plain,
    ( ~ spl3_28
    | spl3_1
    | ~ spl3_4
    | spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f266,f244,f156,f91,f76,f663])).

fof(f76,plain,
    ( spl3_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f156,plain,
    ( spl3_8
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f266,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | spl3_1
    | ~ spl3_4
    | spl3_8
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f78,f93,f158,f246,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f73,f52])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f54,f52])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f158,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f156])).

fof(f78,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f661,plain,
    ( ~ spl3_27
    | spl3_1
    | ~ spl3_3
    | spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f265,f244,f152,f86,f76,f658])).

fof(f152,plain,
    ( spl3_7
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f265,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | spl3_1
    | ~ spl3_3
    | spl3_7
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f78,f88,f154,f246,f74])).

fof(f154,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f152])).

fof(f247,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f167,f91,f86,f244])).

fof(f167,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f88,f93,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f121,f51])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f64,f52])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f223,plain,
    ( spl3_10
    | ~ spl3_4
    | spl3_6 ),
    inference(avatar_split_clause,[],[f161,f103,f91,f220])).

fof(f103,plain,
    ( spl3_6
  <=> v2_struct_0(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f161,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK2,sK2)
    | ~ spl3_4
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f93,f105,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r3_orders_2(k2_yellow_1(X0),X1,X1)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f109,f52])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f108,f47])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f68,f51])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | r3_orders_2(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(condensation,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f105,plain,
    ( ~ v2_struct_0(k2_yellow_1(sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f189,plain,
    ( spl3_9
    | ~ spl3_3
    | spl3_6 ),
    inference(avatar_split_clause,[],[f160,f103,f86,f186])).

fof(f160,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK1,sK1)
    | ~ spl3_3
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f88,f105,f110])).

fof(f159,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | spl3_5 ),
    inference(avatar_split_clause,[],[f107,f98,f156,f152])).

fof(f98,plain,
    ( spl3_5
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f107,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | spl3_5 ),
    inference(resolution,[],[f67,f100])).

fof(f100,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f61])).

fof(f61,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f106,plain,
    ( ~ spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f95,f81,f103])).

fof(f95,plain,
    ( ~ v2_struct_0(k2_yellow_1(sK0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f51,f83,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f101,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f66,f98])).

fof(f66,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) ),
    inference(definition_unfolding,[],[f45,f61])).

fof(f45,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v2_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & v2_lattice3(k2_yellow_1(X0))
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
      & v2_lattice3(k2_yellow_1(sK0))
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
        & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

fof(f94,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f70,f91])).

fof(f70,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f44,f52])).

fof(f44,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f69,f86])).

fof(f69,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f43,f52])).

fof(f43,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f42,f81])).

fof(f42,plain,(
    v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f41,f76])).

fof(f41,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:16:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (28884)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (28886)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (28885)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (28897)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (28888)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (28887)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (28889)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (28894)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (28893)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (28896)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (28895)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (28893)Refutation not found, incomplete strategy% (28893)------------------------------
% 0.22/0.49  % (28893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (28893)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (28893)Memory used [KB]: 10618
% 0.22/0.49  % (28893)Time elapsed: 0.061 s
% 0.22/0.49  % (28893)------------------------------
% 0.22/0.49  % (28893)------------------------------
% 0.22/0.50  % (28892)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (28882)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (28883)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (28899)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (28897)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f704,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f101,f106,f159,f189,f223,f247,f661,f666,f675,f703])).
% 0.22/0.51  fof(f703,plain,(
% 0.22/0.51    ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | spl3_28),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f702])).
% 0.22/0.51  fof(f702,plain,(
% 0.22/0.51    $false | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | spl3_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f695,f361])).
% 0.22/0.51  fof(f361,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11)),
% 0.22/0.51    inference(forward_demodulation,[],[f284,f241])).
% 0.22/0.51  fof(f241,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_10)),
% 0.22/0.51    inference(backward_demodulation,[],[f197,f238])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    sK2 = k11_lattice3(k2_yellow_1(sK0),sK2,sK2) | (~spl3_2 | ~spl3_4 | ~spl3_10)),
% 0.22/0.51    inference(backward_demodulation,[],[f181,f234])).
% 0.22/0.51  fof(f234,plain,(
% 0.22/0.51    sK2 = k12_lattice3(k2_yellow_1(sK0),sK2,sK2) | (~spl3_2 | ~spl3_4 | ~spl3_10)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f93,f93,f83,f222,f140])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_lattice3(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1) )),
% 0.22/0.51    inference(forward_demodulation,[],[f139,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v2_lattice3(k2_yellow_1(X0)) | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1) )),
% 0.22/0.51    inference(forward_demodulation,[],[f138,f52])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v2_lattice3(k2_yellow_1(X0)) | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f137,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v2_lattice3(k2_yellow_1(X0)) | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 | ~v3_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f136,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 | ~v3_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(resolution,[],[f58,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | k12_lattice3(X0,X1,X2) = X1 | ~v3_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((k12_lattice3(X0,X1,X2) = X1 | ~r3_orders_2(X0,X1,X2)) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_0)).
% 0.22/0.51  fof(f222,plain,(
% 0.22/0.51    r3_orders_2(k2_yellow_1(sK0),sK2,sK2) | ~spl3_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f220])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    spl3_10 <=> r3_orders_2(k2_yellow_1(sK0),sK2,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    v2_lattice3(k2_yellow_1(sK0)) | ~spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    spl3_2 <=> v2_lattice3(k2_yellow_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    m1_subset_1(sK2,sK0) | ~spl3_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f91])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    spl3_4 <=> m1_subset_1(sK2,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK2,sK2) = k12_lattice3(k2_yellow_1(sK0),sK2,sK2) | (~spl3_2 | ~spl3_4)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f93,f93,f83,f130])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X0,X1) | ~m1_subset_1(X2,X1) | k11_lattice3(k2_yellow_1(X1),X2,X0) = k12_lattice3(k2_yellow_1(X1),X2,X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f129,f52])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~v2_lattice3(k2_yellow_1(X1)) | k11_lattice3(k2_yellow_1(X1),X2,X0) = k12_lattice3(k2_yellow_1(X1),X2,X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f128,f52])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~v2_lattice3(k2_yellow_1(X1)) | k11_lattice3(k2_yellow_1(X1),X2,X0) = k12_lattice3(k2_yellow_1(X1),X2,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f127,f51])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~l1_orders_2(k2_yellow_1(X1)) | ~v2_lattice3(k2_yellow_1(X1)) | k11_lattice3(k2_yellow_1(X1),X2,X0) = k12_lattice3(k2_yellow_1(X1),X2,X0)) )),
% 0.22/0.51    inference(resolution,[],[f63,f49])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f88,f93,f93,f83,f146])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~v2_lattice3(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X3,X0) | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3) = k11_lattice3(k2_yellow_1(X0),X1,k11_lattice3(k2_yellow_1(X0),X2,X3)) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f145,f52])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,X0) | ~m1_subset_1(X3,X0) | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3) = k11_lattice3(k2_yellow_1(X0),X1,k11_lattice3(k2_yellow_1(X0),X2,X3)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v2_lattice3(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f144,f52])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,X0) | k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3) = k11_lattice3(k2_yellow_1(X0),X1,k11_lattice3(k2_yellow_1(X0),X2,X3)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v2_lattice3(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f143,f52])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3) = k11_lattice3(k2_yellow_1(X0),X1,k11_lattice3(k2_yellow_1(X0),X2,X3)) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v2_lattice3(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f142,f49])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3) = k11_lattice3(k2_yellow_1(X0),X1,k11_lattice3(k2_yellow_1(X0),X2,X3)) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f141,f51])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3) = k11_lattice3(k2_yellow_1(X0),X1,k11_lattice3(k2_yellow_1(X0),X2,X3)) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(resolution,[],[f60,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0] : (v4_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~v4_orders_2(X0) | k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~v4_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~v4_orders_2(X0)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (v4_orders_2(X0) => k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_lattice3)).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    m1_subset_1(sK1,sK0) | ~spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    spl3_3 <=> m1_subset_1(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f284,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | (~spl3_2 | ~spl3_4 | ~spl3_11)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f93,f83,f246,f130])).
% 0.22/0.51  fof(f246,plain,(
% 0.22/0.51    m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~spl3_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f244])).
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    spl3_11 <=> m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.51  fof(f695,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | (~spl3_2 | ~spl3_4 | ~spl3_11 | spl3_28)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f83,f93,f246,f665,f135])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_lattice3(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | k12_lattice3(k2_yellow_1(X0),X1,X2) != X1 | ~m1_subset_1(X1,X0) | r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f134,f52])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k12_lattice3(k2_yellow_1(X0),X1,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v2_lattice3(k2_yellow_1(X0)) | r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f133,f52])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k12_lattice3(k2_yellow_1(X0),X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v2_lattice3(k2_yellow_1(X0)) | r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f132,f47])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k12_lattice3(k2_yellow_1(X0),X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v2_lattice3(k2_yellow_1(X0)) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f131,f51])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k12_lattice3(k2_yellow_1(X0),X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(resolution,[],[f57,f49])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | k12_lattice3(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f665,plain,(
% 0.22/0.51    ~r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | spl3_28),
% 0.22/0.51    inference(avatar_component_clause,[],[f663])).
% 0.22/0.51  fof(f663,plain,(
% 0.22/0.51    spl3_28 <=> r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.51  fof(f675,plain,(
% 0.22/0.51    ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_9 | ~spl3_11 | spl3_27),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f674])).
% 0.22/0.51  fof(f674,plain,(
% 0.22/0.51    $false | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_9 | ~spl3_11 | spl3_27)),
% 0.22/0.51    inference(subsumption_resolution,[],[f667,f362])).
% 0.22/0.51  fof(f362,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_9 | ~spl3_11)),
% 0.22/0.51    inference(forward_demodulation,[],[f283,f233])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_9)),
% 0.22/0.51    inference(backward_demodulation,[],[f204,f232])).
% 0.22/0.51  fof(f232,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_9)),
% 0.22/0.51    inference(forward_demodulation,[],[f229,f174])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f88,f93,f83,f126])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X0,X1) | ~m1_subset_1(X2,X1) | k11_lattice3(k2_yellow_1(X1),X0,X2) = k11_lattice3(k2_yellow_1(X1),X2,X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f125,f52])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~v2_lattice3(k2_yellow_1(X1)) | k11_lattice3(k2_yellow_1(X1),X0,X2) = k11_lattice3(k2_yellow_1(X1),X2,X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f124,f52])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~v2_lattice3(k2_yellow_1(X1)) | k11_lattice3(k2_yellow_1(X1),X0,X2) = k11_lattice3(k2_yellow_1(X1),X2,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f123,f51])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~l1_orders_2(k2_yellow_1(X1)) | ~v2_lattice3(k2_yellow_1(X1)) | k11_lattice3(k2_yellow_1(X1),X0,X2) = k11_lattice3(k2_yellow_1(X1),X2,X0)) )),
% 0.22/0.51    inference(resolution,[],[f59,f49])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_lattice3)).
% 0.22/0.51  fof(f229,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK2,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_9)),
% 0.22/0.51    inference(backward_demodulation,[],[f206,f228])).
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    sK1 = k11_lattice3(k2_yellow_1(sK0),sK1,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_9)),
% 0.22/0.51    inference(backward_demodulation,[],[f178,f224])).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    sK1 = k12_lattice3(k2_yellow_1(sK0),sK1,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_9)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f88,f88,f83,f188,f140])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    r3_orders_2(k2_yellow_1(sK0),sK1,sK1) | ~spl3_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f186])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    spl3_9 <=> r3_orders_2(k2_yellow_1(sK0),sK1,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK1) = k12_lattice3(k2_yellow_1(sK0),sK1,sK1) | (~spl3_2 | ~spl3_3)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f88,f88,f83,f130])).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK1)) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.22/0.51    inference(forward_demodulation,[],[f205,f204])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK1)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.22/0.51    inference(forward_demodulation,[],[f192,f174])).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),sK1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f93,f88,f88,f83,f146])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.22/0.51    inference(forward_demodulation,[],[f193,f174])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f88,f93,f88,f83,f146])).
% 0.22/0.51  fof(f283,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | (~spl3_2 | ~spl3_3 | ~spl3_11)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f88,f83,f246,f130])).
% 0.22/0.51  fof(f667,plain,(
% 0.22/0.51    k11_lattice3(k2_yellow_1(sK0),sK1,sK2) != k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | (~spl3_2 | ~spl3_3 | ~spl3_11 | spl3_27)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f83,f88,f246,f660,f135])).
% 0.22/0.51  fof(f660,plain,(
% 0.22/0.51    ~r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | spl3_27),
% 0.22/0.51    inference(avatar_component_clause,[],[f658])).
% 0.22/0.51  fof(f658,plain,(
% 0.22/0.51    spl3_27 <=> r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.51  fof(f666,plain,(
% 0.22/0.51    ~spl3_28 | spl3_1 | ~spl3_4 | spl3_8 | ~spl3_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f266,f244,f156,f91,f76,f663])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    spl3_1 <=> v1_xboole_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    spl3_8 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.51  fof(f266,plain,(
% 0.22/0.51    ~r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | (spl3_1 | ~spl3_4 | spl3_8 | ~spl3_11)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f78,f93,f158,f246,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f73,f52])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f54,f52])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | spl3_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f156])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ~v1_xboole_0(sK0) | spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f76])).
% 0.22/0.51  fof(f661,plain,(
% 0.22/0.51    ~spl3_27 | spl3_1 | ~spl3_3 | spl3_7 | ~spl3_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f265,f244,f152,f86,f76,f658])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    spl3_7 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.51  fof(f265,plain,(
% 0.22/0.51    ~r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | (spl3_1 | ~spl3_3 | spl3_7 | ~spl3_11)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f78,f88,f154,f246,f74])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | spl3_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f152])).
% 0.22/0.51  fof(f247,plain,(
% 0.22/0.51    spl3_11 | ~spl3_3 | ~spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f167,f91,f86,f244])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | (~spl3_3 | ~spl3_4)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f88,f93,f122])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f121,f51])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(superposition,[],[f64,f52])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    spl3_10 | ~spl3_4 | spl3_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f161,f103,f91,f220])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    spl3_6 <=> v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    r3_orders_2(k2_yellow_1(sK0),sK2,sK2) | (~spl3_4 | spl3_6)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f93,f105,f110])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r3_orders_2(k2_yellow_1(X0),X1,X1) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f109,f52])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f108,f47])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.51    inference(resolution,[],[f68,f51])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_orders_2(X1) | r3_orders_2(X1,X0,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.51    inference(condensation,[],[f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    ~v2_struct_0(k2_yellow_1(sK0)) | spl3_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f103])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    spl3_9 | ~spl3_3 | spl3_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f160,f103,f86,f186])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    r3_orders_2(k2_yellow_1(sK0),sK1,sK1) | (~spl3_3 | spl3_6)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f88,f105,f110])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    ~spl3_7 | ~spl3_8 | spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f107,f98,f156,f152])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    spl3_5 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) | ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | spl3_5),
% 0.22/0.51    inference(resolution,[],[f67,f100])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) | spl3_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f98])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f65,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ~spl3_6 | ~spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f95,f81,f103])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ~v2_struct_0(k2_yellow_1(sK0)) | ~spl3_2),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f51,f83,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    ~spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f66,f98])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2)))),
% 0.22/0.51    inference(definition_unfolding,[],[f45,f61])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f37,f36,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f14])).
% 0.22/0.51  fof(f14,conjecture,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f70,f91])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    m1_subset_1(sK2,sK0)),
% 0.22/0.51    inference(backward_demodulation,[],[f44,f52])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    spl3_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f69,f86])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    m1_subset_1(sK1,sK0)),
% 0.22/0.51    inference(backward_demodulation,[],[f43,f52])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f42,f81])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    v2_lattice3(k2_yellow_1(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ~spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f41,f76])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ~v1_xboole_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (28897)------------------------------
% 0.22/0.51  % (28897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28897)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (28897)Memory used [KB]: 11001
% 0.22/0.51  % (28897)Time elapsed: 0.025 s
% 0.22/0.51  % (28897)------------------------------
% 0.22/0.51  % (28897)------------------------------
% 0.22/0.51  % (28881)Success in time 0.148 s
%------------------------------------------------------------------------------
