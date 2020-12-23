%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 425 expanded)
%              Number of leaves         :   27 ( 156 expanded)
%              Depth                    :   16
%              Number of atoms          :  671 (1403 expanded)
%              Number of equality atoms :   18 ( 131 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f461,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f155,f166,f226,f242,f246,f258,f381,f402,f412,f418,f426,f443,f460])).

fof(f460,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_24 ),
    inference(avatar_contradiction_clause,[],[f459])).

fof(f459,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_24 ),
    inference(subsumption_resolution,[],[f458,f83])).

fof(f83,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f458,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_24 ),
    inference(subsumption_resolution,[],[f456,f78])).

fof(f78,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f456,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,sK0)
    | ~ spl4_2
    | spl4_24 ),
    inference(resolution,[],[f442,f183])).

fof(f183,plain,
    ( ! [X21,X20] :
        ( r1_orders_2(k2_yellow_1(sK0),X20,k13_lattice3(k2_yellow_1(sK0),X20,X21))
        | ~ m1_subset_1(X20,sK0)
        | ~ m1_subset_1(X21,sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f144,f126])).

fof(f126,plain,
    ( ! [X12,X13] :
        ( m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X12,X13),sK0)
        | ~ m1_subset_1(X13,sK0)
        | ~ m1_subset_1(X12,sK0) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f125,f41])).

fof(f41,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f125,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(X13,sK0)
        | ~ m1_subset_1(X12,sK0)
        | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f124,f41])).

fof(f124,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(X12,sK0)
        | ~ m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0)))
        | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f123,f41])).

fof(f123,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0)))
        | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f122,f40])).

fof(f40,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f122,plain,
    ( ! [X12,X13] :
        ( ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0)))
        | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f95,f38])).

fof(f38,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f95,plain,
    ( ! [X12,X13] :
        ( ~ v5_orders_2(k2_yellow_1(sK0))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0)))
        | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_2 ),
    inference(resolution,[],[f73,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_lattice3)).

fof(f73,plain,
    ( v1_lattice3(k2_yellow_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_2
  <=> v1_lattice3(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f144,plain,
    ( ! [X21,X20] :
        ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X20,X21),sK0)
        | ~ m1_subset_1(X21,sK0)
        | ~ m1_subset_1(X20,sK0)
        | r1_orders_2(k2_yellow_1(sK0),X20,k13_lattice3(k2_yellow_1(sK0),X20,X21)) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f143,f41])).

fof(f143,plain,
    ( ! [X21,X20] :
        ( ~ m1_subset_1(X21,sK0)
        | ~ m1_subset_1(X20,sK0)
        | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),X20,k13_lattice3(k2_yellow_1(sK0),X20,X21)) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f142,f41])).

fof(f142,plain,
    ( ! [X21,X20] :
        ( ~ m1_subset_1(X20,sK0)
        | ~ m1_subset_1(X21,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),X20,k13_lattice3(k2_yellow_1(sK0),X20,X21)) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f141,f41])).

fof(f141,plain,
    ( ! [X21,X20] :
        ( ~ m1_subset_1(X20,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X21,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),X20,k13_lattice3(k2_yellow_1(sK0),X20,X21)) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f140,f40])).

fof(f140,plain,
    ( ! [X21,X20] :
        ( ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X20,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X21,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),X20,k13_lattice3(k2_yellow_1(sK0),X20,X21)) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f99,f38])).

fof(f99,plain,
    ( ! [X21,X20] :
        ( ~ v5_orders_2(k2_yellow_1(sK0))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X20,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X21,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),X20,k13_lattice3(k2_yellow_1(sK0),X20,X21)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f73,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X3)
      | k13_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_0)).

fof(f442,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl4_24
  <=> r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f443,plain,
    ( ~ spl4_24
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_22 ),
    inference(avatar_split_clause,[],[f405,f399,f81,f76,f71,f440])).

fof(f399,plain,
    ( spl4_22
  <=> r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f405,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_22 ),
    inference(subsumption_resolution,[],[f404,f78])).

fof(f404,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_4
    | spl4_22 ),
    inference(superposition,[],[f401,f172])).

fof(f172,plain,
    ( ! [X1] :
        ( k13_lattice3(k2_yellow_1(sK0),X1,sK2) = k10_lattice3(k2_yellow_1(sK0),X1,sK2)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(resolution,[],[f130,f83])).

fof(f130,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(X15,sK0)
        | ~ m1_subset_1(X14,sK0)
        | k13_lattice3(k2_yellow_1(sK0),X14,X15) = k10_lattice3(k2_yellow_1(sK0),X14,X15) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f129,f41])).

fof(f129,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(X14,sK0)
        | ~ m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0)))
        | k13_lattice3(k2_yellow_1(sK0),X14,X15) = k10_lattice3(k2_yellow_1(sK0),X14,X15) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f128,f41])).

fof(f128,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0)))
        | k13_lattice3(k2_yellow_1(sK0),X14,X15) = k10_lattice3(k2_yellow_1(sK0),X14,X15) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f127,f40])).

fof(f127,plain,
    ( ! [X14,X15] :
        ( ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0)))
        | k13_lattice3(k2_yellow_1(sK0),X14,X15) = k10_lattice3(k2_yellow_1(sK0),X14,X15) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f96,f38])).

fof(f96,plain,
    ( ! [X14,X15] :
        ( ~ v5_orders_2(k2_yellow_1(sK0))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0)))
        | k13_lattice3(k2_yellow_1(sK0),X14,X15) = k10_lattice3(k2_yellow_1(sK0),X14,X15) )
    | ~ spl4_2 ),
    inference(resolution,[],[f73,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f401,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f399])).

fof(f426,plain,
    ( spl4_1
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | spl4_1
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f424,f68])).

fof(f68,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f424,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_19 ),
    inference(resolution,[],[f376,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f376,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl4_19
  <=> v2_struct_0(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f418,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_23 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_23 ),
    inference(subsumption_resolution,[],[f416,f83])).

fof(f416,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_23 ),
    inference(subsumption_resolution,[],[f414,f78])).

fof(f414,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,sK0)
    | ~ spl4_2
    | spl4_23 ),
    inference(resolution,[],[f411,f178])).

fof(f178,plain,
    ( ! [X19,X18] :
        ( r1_orders_2(k2_yellow_1(sK0),X19,k13_lattice3(k2_yellow_1(sK0),X18,X19))
        | ~ m1_subset_1(X18,sK0)
        | ~ m1_subset_1(X19,sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f139,f126])).

fof(f139,plain,
    ( ! [X19,X18] :
        ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X18,X19),sK0)
        | ~ m1_subset_1(X19,sK0)
        | ~ m1_subset_1(X18,sK0)
        | r1_orders_2(k2_yellow_1(sK0),X19,k13_lattice3(k2_yellow_1(sK0),X18,X19)) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f138,f41])).

% (15065)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f138,plain,
    ( ! [X19,X18] :
        ( ~ m1_subset_1(X19,sK0)
        | ~ m1_subset_1(X18,sK0)
        | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),X19,k13_lattice3(k2_yellow_1(sK0),X18,X19)) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f137,f41])).

fof(f137,plain,
    ( ! [X19,X18] :
        ( ~ m1_subset_1(X18,sK0)
        | ~ m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),X19,k13_lattice3(k2_yellow_1(sK0),X18,X19)) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f136,f41])).

fof(f136,plain,
    ( ! [X19,X18] :
        ( ~ m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),X19,k13_lattice3(k2_yellow_1(sK0),X18,X19)) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f135,f40])).

fof(f135,plain,
    ( ! [X19,X18] :
        ( ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),X19,k13_lattice3(k2_yellow_1(sK0),X18,X19)) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f98,f38])).

fof(f98,plain,
    ( ! [X19,X18] :
        ( ~ v5_orders_2(k2_yellow_1(sK0))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),X19,k13_lattice3(k2_yellow_1(sK0),X18,X19)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f73,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f411,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl4_23
  <=> r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f412,plain,
    ( ~ spl4_23
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_20 ),
    inference(avatar_split_clause,[],[f384,f378,f81,f76,f71,f409])).

fof(f378,plain,
    ( spl4_20
  <=> r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f384,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_20 ),
    inference(subsumption_resolution,[],[f383,f78])).

fof(f383,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_4
    | spl4_20 ),
    inference(superposition,[],[f380,f172])).

fof(f380,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f378])).

fof(f402,plain,
    ( ~ spl4_22
    | ~ spl4_3
    | spl4_10
    | ~ spl4_11
    | spl4_19 ),
    inference(avatar_split_clause,[],[f397,f374,f223,f219,f76,f399])).

fof(f219,plain,
    ( spl4_10
  <=> r3_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f223,plain,
    ( spl4_11
  <=> m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f397,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl4_3
    | spl4_10
    | ~ spl4_11
    | spl4_19 ),
    inference(subsumption_resolution,[],[f396,f375])).

fof(f375,plain,
    ( ~ v2_struct_0(k2_yellow_1(sK0))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f374])).

fof(f396,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ spl4_3
    | spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f236,f224])).

fof(f224,plain,
    ( m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f223])).

fof(f236,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ spl4_3
    | spl4_10 ),
    inference(forward_demodulation,[],[f235,f41])).

fof(f235,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ spl4_3
    | spl4_10 ),
    inference(subsumption_resolution,[],[f234,f78])).

fof(f234,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | v2_struct_0(k2_yellow_1(sK0))
    | spl4_10 ),
    inference(forward_demodulation,[],[f233,f41])).

fof(f233,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | v2_struct_0(k2_yellow_1(sK0))
    | spl4_10 ),
    inference(subsumption_resolution,[],[f232,f40])).

fof(f232,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | v2_struct_0(k2_yellow_1(sK0))
    | spl4_10 ),
    inference(subsumption_resolution,[],[f230,f36])).

fof(f36,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f230,plain,
    ( ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | v2_struct_0(k2_yellow_1(sK0))
    | spl4_10 ),
    inference(resolution,[],[f221,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f221,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f219])).

fof(f381,plain,
    ( spl4_19
    | ~ spl4_20
    | ~ spl4_4
    | ~ spl4_11
    | spl4_13 ),
    inference(avatar_split_clause,[],[f267,f255,f223,f81,f378,f374])).

fof(f255,plain,
    ( spl4_13
  <=> r3_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f267,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ spl4_4
    | ~ spl4_11
    | spl4_13 ),
    inference(subsumption_resolution,[],[f266,f224])).

fof(f266,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ spl4_4
    | spl4_13 ),
    inference(forward_demodulation,[],[f265,f41])).

fof(f265,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ spl4_4
    | spl4_13 ),
    inference(subsumption_resolution,[],[f264,f83])).

fof(f264,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | v2_struct_0(k2_yellow_1(sK0))
    | spl4_13 ),
    inference(forward_demodulation,[],[f263,f41])).

fof(f263,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | v2_struct_0(k2_yellow_1(sK0))
    | spl4_13 ),
    inference(subsumption_resolution,[],[f262,f40])).

fof(f262,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | v2_struct_0(k2_yellow_1(sK0))
    | spl4_13 ),
    inference(subsumption_resolution,[],[f260,f36])).

fof(f260,plain,
    ( ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | v2_struct_0(k2_yellow_1(sK0))
    | spl4_13 ),
    inference(resolution,[],[f257,f54])).

fof(f257,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f255])).

fof(f258,plain,
    ( ~ spl4_13
    | spl4_1
    | ~ spl4_4
    | spl4_7
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f253,f223,f163,f81,f66,f255])).

fof(f163,plain,
    ( spl4_7
  <=> r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f253,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_1
    | ~ spl4_4
    | spl4_7
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f170,f224])).

fof(f170,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ r3_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_1
    | ~ spl4_4
    | spl4_7 ),
    inference(subsumption_resolution,[],[f169,f83])).

fof(f169,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ r3_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_1
    | spl4_7 ),
    inference(resolution,[],[f165,f90])).

fof(f90,plain,
    ( ! [X2,X3] :
        ( r1_tarski(X2,X3)
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X3,sK0)
        | ~ r3_orders_2(k2_yellow_1(sK0),X2,X3) )
    | spl4_1 ),
    inference(forward_demodulation,[],[f89,f41])).

fof(f89,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X2,X3)
        | ~ r3_orders_2(k2_yellow_1(sK0),X2,X3) )
    | spl4_1 ),
    inference(forward_demodulation,[],[f86,f41])).

fof(f86,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X2,X3)
        | ~ r3_orders_2(k2_yellow_1(sK0),X2,X3) )
    | spl4_1 ),
    inference(resolution,[],[f68,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f165,plain,
    ( ~ r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f163])).

fof(f246,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_12 ),
    inference(subsumption_resolution,[],[f244,f78])).

fof(f244,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_4
    | spl4_12 ),
    inference(subsumption_resolution,[],[f243,f83])).

fof(f243,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | ~ spl4_2
    | spl4_12 ),
    inference(resolution,[],[f241,f126])).

fof(f241,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl4_12
  <=> m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f242,plain,
    ( ~ spl4_12
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_11 ),
    inference(avatar_split_clause,[],[f228,f223,f81,f76,f71,f239])).

fof(f228,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_11 ),
    inference(subsumption_resolution,[],[f227,f78])).

fof(f227,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_4
    | spl4_11 ),
    inference(superposition,[],[f225,f172])).

fof(f225,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f223])).

fof(f226,plain,
    ( ~ spl4_10
    | ~ spl4_11
    | spl4_1
    | ~ spl4_3
    | spl4_6 ),
    inference(avatar_split_clause,[],[f168,f159,f76,f66,f223,f219])).

fof(f159,plain,
    ( spl4_6
  <=> r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f168,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ r3_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_1
    | ~ spl4_3
    | spl4_6 ),
    inference(subsumption_resolution,[],[f167,f78])).

fof(f167,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ r3_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_1
    | spl4_6 ),
    inference(resolution,[],[f161,f90])).

fof(f161,plain,
    ( ~ r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f159])).

fof(f166,plain,
    ( ~ spl4_6
    | ~ spl4_7
    | spl4_5 ),
    inference(avatar_split_clause,[],[f156,f152,f163,f159])).

fof(f152,plain,
    ( spl4_5
  <=> r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f156,plain,
    ( ~ r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_5 ),
    inference(resolution,[],[f154,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f154,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f152])).

fof(f155,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f31,f152])).

fof(f31,plain,(
    ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v1_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_1)).

fof(f84,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f64,f81])).

fof(f64,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f30,f41])).

fof(f30,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f63,f76])).

fof(f63,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f32,f41])).

fof(f32,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f74,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f34,f71])).

fof(f34,plain,(
    v1_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f33,f66])).

fof(f33,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:02:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.43  % (15075)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.43  % (15067)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.43  % (15075)Refutation not found, incomplete strategy% (15075)------------------------------
% 0.21/0.43  % (15075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (15075)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.43  
% 0.21/0.43  % (15075)Memory used [KB]: 6268
% 0.21/0.43  % (15075)Time elapsed: 0.008 s
% 0.21/0.43  % (15075)------------------------------
% 0.21/0.43  % (15075)------------------------------
% 0.21/0.46  % (15069)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (15077)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (15071)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.46  % (15061)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (15063)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (15071)Refutation not found, incomplete strategy% (15071)------------------------------
% 0.21/0.47  % (15071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (15073)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (15063)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (15071)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (15071)Memory used [KB]: 10618
% 0.21/0.48  % (15071)Time elapsed: 0.052 s
% 0.21/0.48  % (15071)------------------------------
% 0.21/0.48  % (15071)------------------------------
% 0.21/0.48  % (15061)Refutation not found, incomplete strategy% (15061)------------------------------
% 0.21/0.48  % (15061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (15061)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (15061)Memory used [KB]: 10618
% 0.21/0.48  % (15061)Time elapsed: 0.062 s
% 0.21/0.48  % (15061)------------------------------
% 0.21/0.48  % (15061)------------------------------
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f461,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f155,f166,f226,f242,f246,f258,f381,f402,f412,f418,f426,f443,f460])).
% 0.21/0.48  fof(f460,plain,(
% 0.21/0.48    ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_24),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f459])).
% 0.21/0.48  fof(f459,plain,(
% 0.21/0.48    $false | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f458,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    m1_subset_1(sK2,sK0) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl4_4 <=> m1_subset_1(sK2,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f458,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,sK0) | (~spl4_2 | ~spl4_3 | spl4_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f456,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    m1_subset_1(sK1,sK0) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl4_3 <=> m1_subset_1(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f456,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,sK0) | (~spl4_2 | spl4_24)),
% 0.21/0.48    inference(resolution,[],[f442,f183])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    ( ! [X21,X20] : (r1_orders_2(k2_yellow_1(sK0),X20,k13_lattice3(k2_yellow_1(sK0),X20,X21)) | ~m1_subset_1(X20,sK0) | ~m1_subset_1(X21,sK0)) ) | ~spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f144,f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ( ! [X12,X13] : (m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X12,X13),sK0) | ~m1_subset_1(X13,sK0) | ~m1_subset_1(X12,sK0)) ) | ~spl4_2),
% 0.21/0.48    inference(forward_demodulation,[],[f125,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    ( ! [X12,X13] : (~m1_subset_1(X13,sK0) | ~m1_subset_1(X12,sK0) | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl4_2),
% 0.21/0.48    inference(forward_demodulation,[],[f124,f41])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ( ! [X12,X13] : (~m1_subset_1(X12,sK0) | ~m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0))) | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl4_2),
% 0.21/0.48    inference(forward_demodulation,[],[f123,f41])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ( ! [X12,X13] : (~m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0))) | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f122,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    ( ! [X12,X13] : (~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0))) | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f95,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X12,X13] : (~v5_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0))) | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X12,X13),u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f73,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_lattice3(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_lattice3)).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    v1_lattice3(k2_yellow_1(sK0)) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl4_2 <=> v1_lattice3(k2_yellow_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X21,X20] : (~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X20,X21),sK0) | ~m1_subset_1(X21,sK0) | ~m1_subset_1(X20,sK0) | r1_orders_2(k2_yellow_1(sK0),X20,k13_lattice3(k2_yellow_1(sK0),X20,X21))) ) | ~spl4_2),
% 0.21/0.48    inference(forward_demodulation,[],[f143,f41])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    ( ! [X21,X20] : (~m1_subset_1(X21,sK0) | ~m1_subset_1(X20,sK0) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),X20,k13_lattice3(k2_yellow_1(sK0),X20,X21))) ) | ~spl4_2),
% 0.21/0.48    inference(forward_demodulation,[],[f142,f41])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ( ! [X21,X20] : (~m1_subset_1(X20,sK0) | ~m1_subset_1(X21,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),X20,k13_lattice3(k2_yellow_1(sK0),X20,X21))) ) | ~spl4_2),
% 0.21/0.48    inference(forward_demodulation,[],[f141,f41])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ( ! [X21,X20] : (~m1_subset_1(X20,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X21,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),X20,k13_lattice3(k2_yellow_1(sK0),X20,X21))) ) | ~spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f140,f40])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    ( ! [X21,X20] : (~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X20,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X21,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),X20,k13_lattice3(k2_yellow_1(sK0),X20,X21))) ) | ~spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f99,f38])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ( ! [X21,X20] : (~v5_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X20,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X21,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X20,X21),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),X20,k13_lattice3(k2_yellow_1(sK0),X20,X21))) ) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f73,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_lattice3(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X1,X3) | k13_lattice3(X0,X1,X2) != X3) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_0)).
% 0.21/0.48  fof(f442,plain,(
% 0.21/0.48    ~r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f440])).
% 0.21/0.48  fof(f440,plain,(
% 0.21/0.48    spl4_24 <=> r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.48  fof(f443,plain,(
% 0.21/0.48    ~spl4_24 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_22),
% 0.21/0.48    inference(avatar_split_clause,[],[f405,f399,f81,f76,f71,f440])).
% 0.21/0.48  fof(f399,plain,(
% 0.21/0.48    spl4_22 <=> r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.48  fof(f405,plain,(
% 0.21/0.48    ~r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_22)),
% 0.21/0.48    inference(subsumption_resolution,[],[f404,f78])).
% 0.21/0.48  fof(f404,plain,(
% 0.21/0.48    ~r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK1,sK0) | (~spl4_2 | ~spl4_4 | spl4_22)),
% 0.21/0.48    inference(superposition,[],[f401,f172])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    ( ! [X1] : (k13_lattice3(k2_yellow_1(sK0),X1,sK2) = k10_lattice3(k2_yellow_1(sK0),X1,sK2) | ~m1_subset_1(X1,sK0)) ) | (~spl4_2 | ~spl4_4)),
% 0.21/0.48    inference(resolution,[],[f130,f83])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ( ! [X14,X15] : (~m1_subset_1(X15,sK0) | ~m1_subset_1(X14,sK0) | k13_lattice3(k2_yellow_1(sK0),X14,X15) = k10_lattice3(k2_yellow_1(sK0),X14,X15)) ) | ~spl4_2),
% 0.21/0.48    inference(forward_demodulation,[],[f129,f41])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    ( ! [X14,X15] : (~m1_subset_1(X14,sK0) | ~m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0))) | k13_lattice3(k2_yellow_1(sK0),X14,X15) = k10_lattice3(k2_yellow_1(sK0),X14,X15)) ) | ~spl4_2),
% 0.21/0.48    inference(forward_demodulation,[],[f128,f41])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ( ! [X14,X15] : (~m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0))) | k13_lattice3(k2_yellow_1(sK0),X14,X15) = k10_lattice3(k2_yellow_1(sK0),X14,X15)) ) | ~spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f127,f40])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ( ! [X14,X15] : (~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0))) | k13_lattice3(k2_yellow_1(sK0),X14,X15) = k10_lattice3(k2_yellow_1(sK0),X14,X15)) ) | ~spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f38])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X14,X15] : (~v5_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0))) | k13_lattice3(k2_yellow_1(sK0),X14,X15) = k10_lattice3(k2_yellow_1(sK0),X14,X15)) ) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f73,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_lattice3(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.21/0.48  fof(f401,plain,(
% 0.21/0.48    ~r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f399])).
% 0.21/0.48  fof(f426,plain,(
% 0.21/0.48    spl4_1 | ~spl4_19),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f425])).
% 0.21/0.48  fof(f425,plain,(
% 0.21/0.48    $false | (spl4_1 | ~spl4_19)),
% 0.21/0.48    inference(subsumption_resolution,[],[f424,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~v1_xboole_0(sK0) | spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl4_1 <=> v1_xboole_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f424,plain,(
% 0.21/0.48    v1_xboole_0(sK0) | ~spl4_19),
% 0.21/0.48    inference(resolution,[],[f376,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : ((v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.21/0.48  fof(f376,plain,(
% 0.21/0.48    v2_struct_0(k2_yellow_1(sK0)) | ~spl4_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f374])).
% 0.21/0.48  fof(f374,plain,(
% 0.21/0.48    spl4_19 <=> v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.48  fof(f418,plain,(
% 0.21/0.48    ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_23),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f417])).
% 0.21/0.48  fof(f417,plain,(
% 0.21/0.48    $false | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f416,f83])).
% 0.21/0.48  fof(f416,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,sK0) | (~spl4_2 | ~spl4_3 | spl4_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f414,f78])).
% 0.21/0.48  fof(f414,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,sK0) | (~spl4_2 | spl4_23)),
% 0.21/0.48    inference(resolution,[],[f411,f178])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    ( ! [X19,X18] : (r1_orders_2(k2_yellow_1(sK0),X19,k13_lattice3(k2_yellow_1(sK0),X18,X19)) | ~m1_subset_1(X18,sK0) | ~m1_subset_1(X19,sK0)) ) | ~spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f139,f126])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ( ! [X19,X18] : (~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X18,X19),sK0) | ~m1_subset_1(X19,sK0) | ~m1_subset_1(X18,sK0) | r1_orders_2(k2_yellow_1(sK0),X19,k13_lattice3(k2_yellow_1(sK0),X18,X19))) ) | ~spl4_2),
% 0.21/0.48    inference(forward_demodulation,[],[f138,f41])).
% 0.21/0.48  % (15065)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ( ! [X19,X18] : (~m1_subset_1(X19,sK0) | ~m1_subset_1(X18,sK0) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),X19,k13_lattice3(k2_yellow_1(sK0),X18,X19))) ) | ~spl4_2),
% 0.21/0.48    inference(forward_demodulation,[],[f137,f41])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ( ! [X19,X18] : (~m1_subset_1(X18,sK0) | ~m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),X19,k13_lattice3(k2_yellow_1(sK0),X18,X19))) ) | ~spl4_2),
% 0.21/0.48    inference(forward_demodulation,[],[f136,f41])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ( ! [X19,X18] : (~m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),X19,k13_lattice3(k2_yellow_1(sK0),X18,X19))) ) | ~spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f135,f40])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ( ! [X19,X18] : (~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),X19,k13_lattice3(k2_yellow_1(sK0),X18,X19))) ) | ~spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f98,f38])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X19,X18] : (~v5_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X18,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X19,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X18,X19),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),X19,k13_lattice3(k2_yellow_1(sK0),X18,X19))) ) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f73,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_lattice3(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X2,X3) | k13_lattice3(X0,X1,X2) != X3) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f411,plain,(
% 0.21/0.48    ~r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f409])).
% 0.21/0.48  fof(f409,plain,(
% 0.21/0.48    spl4_23 <=> r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.48  fof(f412,plain,(
% 0.21/0.48    ~spl4_23 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f384,f378,f81,f76,f71,f409])).
% 0.21/0.48  fof(f378,plain,(
% 0.21/0.48    spl4_20 <=> r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.48  fof(f384,plain,(
% 0.21/0.48    ~r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f383,f78])).
% 0.21/0.48  fof(f383,plain,(
% 0.21/0.48    ~r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK1,sK0) | (~spl4_2 | ~spl4_4 | spl4_20)),
% 0.21/0.48    inference(superposition,[],[f380,f172])).
% 0.21/0.48  fof(f380,plain,(
% 0.21/0.48    ~r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f378])).
% 0.21/0.48  fof(f402,plain,(
% 0.21/0.48    ~spl4_22 | ~spl4_3 | spl4_10 | ~spl4_11 | spl4_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f397,f374,f223,f219,f76,f399])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    spl4_10 <=> r3_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    spl4_11 <=> m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f397,plain,(
% 0.21/0.48    ~r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (~spl4_3 | spl4_10 | ~spl4_11 | spl4_19)),
% 0.21/0.48    inference(subsumption_resolution,[],[f396,f375])).
% 0.21/0.48  fof(f375,plain,(
% 0.21/0.48    ~v2_struct_0(k2_yellow_1(sK0)) | spl4_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f374])).
% 0.21/0.48  fof(f396,plain,(
% 0.21/0.48    ~r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | v2_struct_0(k2_yellow_1(sK0)) | (~spl4_3 | spl4_10 | ~spl4_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f236,f224])).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f223])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | v2_struct_0(k2_yellow_1(sK0)) | (~spl4_3 | spl4_10)),
% 0.21/0.48    inference(forward_demodulation,[],[f235,f41])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | v2_struct_0(k2_yellow_1(sK0)) | (~spl4_3 | spl4_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f234,f78])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | v2_struct_0(k2_yellow_1(sK0)) | spl4_10),
% 0.21/0.48    inference(forward_demodulation,[],[f233,f41])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | v2_struct_0(k2_yellow_1(sK0)) | spl4_10),
% 0.21/0.48    inference(subsumption_resolution,[],[f232,f40])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | v2_struct_0(k2_yellow_1(sK0)) | spl4_10),
% 0.21/0.48    inference(subsumption_resolution,[],[f230,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | v2_struct_0(k2_yellow_1(sK0)) | spl4_10),
% 0.21/0.48    inference(resolution,[],[f221,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    ~r3_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f219])).
% 0.21/0.48  fof(f381,plain,(
% 0.21/0.48    spl4_19 | ~spl4_20 | ~spl4_4 | ~spl4_11 | spl4_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f267,f255,f223,f81,f378,f374])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    spl4_13 <=> r3_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    ~r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | v2_struct_0(k2_yellow_1(sK0)) | (~spl4_4 | ~spl4_11 | spl4_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f266,f224])).
% 0.21/0.48  fof(f266,plain,(
% 0.21/0.48    ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | v2_struct_0(k2_yellow_1(sK0)) | (~spl4_4 | spl4_13)),
% 0.21/0.48    inference(forward_demodulation,[],[f265,f41])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | v2_struct_0(k2_yellow_1(sK0)) | (~spl4_4 | spl4_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f264,f83])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | v2_struct_0(k2_yellow_1(sK0)) | spl4_13),
% 0.21/0.48    inference(forward_demodulation,[],[f263,f41])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | v2_struct_0(k2_yellow_1(sK0)) | spl4_13),
% 0.21/0.48    inference(subsumption_resolution,[],[f262,f40])).
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | v2_struct_0(k2_yellow_1(sK0)) | spl4_13),
% 0.21/0.48    inference(subsumption_resolution,[],[f260,f36])).
% 0.21/0.48  fof(f260,plain,(
% 0.21/0.48    ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | v2_struct_0(k2_yellow_1(sK0)) | spl4_13),
% 0.21/0.48    inference(resolution,[],[f257,f54])).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    ~r3_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f255])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    ~spl4_13 | spl4_1 | ~spl4_4 | spl4_7 | ~spl4_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f253,f223,f163,f81,f66,f255])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    spl4_7 <=> r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    ~r3_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (spl4_1 | ~spl4_4 | spl4_7 | ~spl4_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f170,f224])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~r3_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (spl4_1 | ~spl4_4 | spl4_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f169,f83])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~r3_orders_2(k2_yellow_1(sK0),sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (spl4_1 | spl4_7)),
% 0.21/0.48    inference(resolution,[],[f165,f90])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X3,sK0) | ~r3_orders_2(k2_yellow_1(sK0),X2,X3)) ) | spl4_1),
% 0.21/0.48    inference(forward_demodulation,[],[f89,f41])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~m1_subset_1(X2,sK0) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X2,X3) | ~r3_orders_2(k2_yellow_1(sK0),X2,X3)) ) | spl4_1),
% 0.21/0.48    inference(forward_demodulation,[],[f86,f41])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X2,X3) | ~r3_orders_2(k2_yellow_1(sK0),X2,X3)) ) | spl4_1),
% 0.21/0.48    inference(resolution,[],[f68,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    ~r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f163])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_12),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f245])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    $false | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f244,f78])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,sK0) | (~spl4_2 | ~spl4_4 | spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f243,f83])).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0) | (~spl4_2 | spl4_12)),
% 0.21/0.48    inference(resolution,[],[f241,f126])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | spl4_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f239])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    spl4_12 <=> m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    ~spl4_12 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f228,f223,f81,f76,f71,f239])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f227,f78])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~m1_subset_1(sK1,sK0) | (~spl4_2 | ~spl4_4 | spl4_11)),
% 0.21/0.48    inference(superposition,[],[f225,f172])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f223])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    ~spl4_10 | ~spl4_11 | spl4_1 | ~spl4_3 | spl4_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f168,f159,f76,f66,f223,f219])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    spl4_6 <=> r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~r3_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (spl4_1 | ~spl4_3 | spl4_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f167,f78])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | ~r3_orders_2(k2_yellow_1(sK0),sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (spl4_1 | spl4_6)),
% 0.21/0.48    inference(resolution,[],[f161,f90])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    ~r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f159])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    ~spl4_6 | ~spl4_7 | spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f156,f152,f163,f159])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    spl4_5 <=> r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    ~r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_5),
% 0.21/0.48    inference(resolution,[],[f154,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f152])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ~spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f152])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_1)).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f64,f81])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    m1_subset_1(sK2,sK0)),
% 0.21/0.48    inference(forward_demodulation,[],[f30,f41])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f63,f76])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    m1_subset_1(sK1,sK0)),
% 0.21/0.48    inference(forward_demodulation,[],[f32,f41])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f71])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    v1_lattice3(k2_yellow_1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ~spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f66])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ~v1_xboole_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (15063)------------------------------
% 0.21/0.48  % (15063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (15063)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (15063)Memory used [KB]: 10874
% 0.21/0.48  % (15063)Time elapsed: 0.074 s
% 0.21/0.48  % (15063)------------------------------
% 0.21/0.48  % (15063)------------------------------
% 0.21/0.48  % (15059)Success in time 0.131 s
%------------------------------------------------------------------------------
