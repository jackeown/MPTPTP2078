%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:34 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  302 (1428 expanded)
%              Number of leaves         :   37 ( 462 expanded)
%              Depth                    :   38
%              Number of atoms          : 2310 (8272 expanded)
%              Number of equality atoms :  187 ( 437 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3586,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f96,f125,f130,f136,f141,f157,f174,f189,f457,f988,f1049,f1065,f1248,f1332,f2061,f2139,f2176,f2368,f3027,f3050,f3583,f3584,f3585])).

fof(f3585,plain,
    ( k11_lattice3(sK0,sK1,sK2) != sK5(sK0,sK2,sK1)
    | sK5(sK0,sK1,sK2) != sK5(sK0,sK2,sK1)
    | m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3584,plain,
    ( k11_lattice3(sK0,sK1,sK2) != sK5(sK0,sK2,sK1)
    | sK5(sK0,sK1,sK2) != sK5(sK0,sK2,sK1)
    | sK2 != k10_lattice3(sK0,sK5(sK0,sK2,sK1),sK2)
    | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK1,sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3583,plain,
    ( spl9_65
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_9
    | ~ spl9_45 ),
    inference(avatar_split_clause,[],[f3560,f2106,f138,f127,f122,f93,f88,f78,f3580])).

fof(f3580,plain,
    ( spl9_65
  <=> k11_lattice3(sK0,sK1,sK2) = sK5(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).

fof(f78,plain,
    ( spl9_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f88,plain,
    ( spl9_4
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f93,plain,
    ( spl9_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f122,plain,
    ( spl9_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f127,plain,
    ( spl9_7
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f138,plain,
    ( spl9_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f2106,plain,
    ( spl9_45
  <=> m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f3560,plain,
    ( k11_lattice3(sK0,sK1,sK2) = sK5(sK0,sK2,sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_9
    | ~ spl9_45 ),
    inference(subsumption_resolution,[],[f3547,f129])).

fof(f129,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f3547,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k11_lattice3(sK0,sK1,sK2) = sK5(sK0,sK2,sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9
    | ~ spl9_45 ),
    inference(resolution,[],[f3501,f2107])).

fof(f2107,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl9_45 ),
    inference(avatar_component_clause,[],[f2106])).

fof(f3501,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK2,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k11_lattice3(sK0,X0,sK2) = sK5(sK0,sK2,X0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(resolution,[],[f2235,f124])).

fof(f124,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f2235,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f2234,f144])).

fof(f144,plain,
    ( ! [X6,X5] :
        ( r1_orders_2(sK0,sK5(sK0,X5,X6),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f114,f95])).

fof(f95,plain,
    ( l1_orders_2(sK0)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f114,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK5(sK0,X5,X6),X6)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f90,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r1_orders_2(X0,X4,X2)
                            & r1_orders_2(X0,X4,X1) )
                         => r1_orders_2(X0,X4,X3) ) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattice3)).

fof(f90,plain,
    ( v2_lattice3(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f2234,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X3) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f2231,f143])).

fof(f143,plain,
    ( ! [X4,X3] :
        ( r1_orders_2(sK0,sK5(sK0,X3,X4),X3)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f113,f95])).

fof(f113,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK5(sK0,X3,X4),X3)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f90,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,sK5(X0,X1,X2),X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2231,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X3) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f2221])).

fof(f2221,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f1327,f223])).

fof(f223,plain,
    ( ! [X14,X12,X13] :
        ( r1_orders_2(sK0,sK8(sK0,X12,X13,X14),X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X14,X12)
        | ~ r1_orders_2(sK0,X14,X13)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | k11_lattice3(sK0,X12,X13) = X14 )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f222,f95])).

fof(f222,plain,
    ( ! [X14,X12,X13] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X14,X12)
        | ~ r1_orders_2(sK0,X14,X13)
        | r1_orders_2(sK0,sK8(sK0,X12,X13,X14),X13)
        | k11_lattice3(sK0,X12,X13) = X14 )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f109,f90])).

fof(f109,plain,
    ( ! [X14,X12,X13] :
        ( ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X14,X12)
        | ~ r1_orders_2(sK0,X14,X13)
        | r1_orders_2(sK0,sK8(sK0,X12,X13,X14),X13)
        | k11_lattice3(sK0,X12,X13) = X14 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f101,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f101,plain,
    ( ! [X14,X12,X13] :
        ( v2_struct_0(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X14,X12)
        | ~ r1_orders_2(sK0,X14,X13)
        | r1_orders_2(sK0,sK8(sK0,X12,X13,X14),X13)
        | k11_lattice3(sK0,X12,X13) = X14 )
    | ~ spl9_2 ),
    inference(resolution,[],[f80,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | r1_orders_2(X0,sK8(X0,X1,X2,X3),X2)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f80,plain,
    ( v5_orders_2(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f1327,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X1,X2)),X1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k11_lattice3(sK0,X2,X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f1326,f90])).

fof(f1326,plain,
    ( ! [X2,X3,X1] :
        ( sK5(sK0,X1,X2) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X1,X2)),X1)
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f1323,f95])).

fof(f1323,plain,
    ( ! [X2,X3,X1] :
        ( sK5(sK0,X1,X2) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X1,X2)),X1)
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f1314])).

fof(f1314,plain,
    ( ! [X2,X3,X1] :
        ( sK5(sK0,X1,X2) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X1,X2)),X1)
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f1039,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1039,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0))
        | sK5(sK0,X1,X0) = k11_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X0,X2,sK5(sK0,X1,X0)),X1)
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X0),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f1038,f144])).

fof(f1038,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X0) = k11_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X0,X2,sK5(sK0,X1,X0)),X1)
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X0),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X0),X0)
        | ~ m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f1029])).

fof(f1029,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X0) = k11_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X0,X2,sK5(sK0,X1,X0)),X1)
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X0),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X0),X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X0),X0)
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X0),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X0) = k11_lattice3(sK0,X0,X2) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f701,f199])).

fof(f199,plain,
    ( ! [X10,X11,X9] :
        ( r1_orders_2(sK0,sK8(sK0,X9,X10,X11),X9)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X11,X9)
        | ~ r1_orders_2(sK0,X11,X10)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k11_lattice3(sK0,X9,X10) = X11 )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f198,f95])).

fof(f198,plain,
    ( ! [X10,X11,X9] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X11,X9)
        | ~ r1_orders_2(sK0,X11,X10)
        | r1_orders_2(sK0,sK8(sK0,X9,X10,X11),X9)
        | k11_lattice3(sK0,X9,X10) = X11 )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f108,f90])).

fof(f108,plain,
    ( ! [X10,X11,X9] :
        ( ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X11,X9)
        | ~ r1_orders_2(sK0,X11,X10)
        | r1_orders_2(sK0,sK8(sK0,X9,X10,X11),X9)
        | k11_lattice3(sK0,X9,X10) = X11 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f100,f38])).

fof(f100,plain,
    ( ! [X10,X11,X9] :
        ( v2_struct_0(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X11,X9)
        | ~ r1_orders_2(sK0,X11,X10)
        | r1_orders_2(sK0,sK8(sK0,X9,X10,X11),X9)
        | k11_lattice3(sK0,X9,X10) = X11 )
    | ~ spl9_2 ),
    inference(resolution,[],[f80,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | r1_orders_2(X0,sK8(X0,X1,X2,X3),X1)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f701,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK8(sK0,X3,X2,sK5(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X3,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X3,X2,sK5(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f700,f90])).

fof(f700,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X3,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X3,X2,sK5(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,sK8(sK0,X3,X2,sK5(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f699,f95])).

fof(f699,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X3,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X3,X2,sK5(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,sK8(sK0,X3,X2,sK5(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f694])).

fof(f694,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X3,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X3,X2,sK5(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,sK8(sK0,X3,X2,sK5(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f417,f44])).

fof(f417,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f416,f140])).

fof(f140,plain,
    ( ~ v2_struct_0(sK0)
    | spl9_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f416,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f415,f95])).

fof(f415,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f414,f90])).

fof(f414,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f413,f80])).

fof(f413,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f412])).

fof(f412,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | v2_struct_0(sK0)
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(resolution,[],[f287,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | v2_struct_0(X0)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f287,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK8(sK0,X3,X0,sK5(sK0,X1,X2)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k11_lattice3(sK0,X3,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X3,X0,sK5(sK0,X1,X2)),X1)
        | ~ r1_orders_2(sK0,sK8(sK0,X3,X0,sK5(sK0,X1,X2)),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f286,f90])).

fof(f286,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k11_lattice3(sK0,X3,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,X3,X0,sK5(sK0,X1,X2)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X3,X0,sK5(sK0,X1,X2)),X1)
        | ~ r1_orders_2(sK0,sK8(sK0,X3,X0,sK5(sK0,X1,X2)),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f285,f95])).

fof(f285,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k11_lattice3(sK0,X3,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,X3,X0,sK5(sK0,X1,X2)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X3,X0,sK5(sK0,X1,X2)),X1)
        | ~ r1_orders_2(sK0,sK8(sK0,X3,X0,sK5(sK0,X1,X2)),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f284])).

fof(f284,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k11_lattice3(sK0,X3,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,X3,X0,sK5(sK0,X1,X2)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X3,X0,sK5(sK0,X1,X2)),X1)
        | ~ r1_orders_2(sK0,sK8(sK0,X3,X0,sK5(sK0,X1,X2)),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(resolution,[],[f240,f44])).

fof(f240,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ m1_subset_1(sK5(sK0,X5,X6),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X5,X6),X7)
        | ~ r1_orders_2(sK0,sK5(sK0,X5,X6),X4)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | sK5(sK0,X5,X6) = k11_lattice3(sK0,X7,X4)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,X7,X4,sK5(sK0,X5,X6)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK8(sK0,X7,X4,sK5(sK0,X5,X6)),X5)
        | ~ r1_orders_2(sK0,sK8(sK0,X7,X4,sK5(sK0,X5,X6)),X6)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(resolution,[],[f233,f169])).

fof(f169,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X2,sK5(sK0,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f112,f95])).

fof(f112,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X2,X1)
        | r1_orders_2(sK0,X2,sK5(sK0,X0,X1))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f90,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X4,X1)
      | ~ r1_orders_2(X0,X4,X2)
      | r1_orders_2(X0,X4,sK5(X0,X1,X2))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f233,plain,
    ( ! [X17,X15,X16] :
        ( ~ r1_orders_2(sK0,sK8(sK0,X15,X16,X17),X17)
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X17,X15)
        | ~ r1_orders_2(sK0,X17,X16)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | k11_lattice3(sK0,X15,X16) = X17 )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f232,f95])).

fof(f232,plain,
    ( ! [X17,X15,X16] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X17,X15)
        | ~ r1_orders_2(sK0,X17,X16)
        | ~ r1_orders_2(sK0,sK8(sK0,X15,X16,X17),X17)
        | k11_lattice3(sK0,X15,X16) = X17 )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f110,f90])).

fof(f110,plain,
    ( ! [X17,X15,X16] :
        ( ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X17,X15)
        | ~ r1_orders_2(sK0,X17,X16)
        | ~ r1_orders_2(sK0,sK8(sK0,X15,X16,X17),X17)
        | k11_lattice3(sK0,X15,X16) = X17 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f102,f38])).

fof(f102,plain,
    ( ! [X17,X15,X16] :
        ( v2_struct_0(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X17,X15)
        | ~ r1_orders_2(sK0,X17,X16)
        | ~ r1_orders_2(sK0,sK8(sK0,X15,X16,X17),X17)
        | k11_lattice3(sK0,X15,X16) = X17 )
    | ~ spl9_2 ),
    inference(resolution,[],[f80,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,sK8(X0,X1,X2,X3),X3)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3050,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_23
    | ~ spl9_24
    | ~ spl9_29
    | spl9_59 ),
    inference(avatar_contradiction_clause,[],[f3049])).

fof(f3049,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_23
    | ~ spl9_24
    | ~ spl9_29
    | spl9_59 ),
    inference(subsumption_resolution,[],[f3048,f124])).

fof(f3048,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_23
    | ~ spl9_24
    | ~ spl9_29
    | spl9_59 ),
    inference(subsumption_resolution,[],[f3047,f1048])).

fof(f1048,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK1)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f1046])).

fof(f1046,plain,
    ( spl9_24
  <=> r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f3047,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_23
    | ~ spl9_29
    | spl9_59 ),
    inference(subsumption_resolution,[],[f3046,f1331])).

fof(f1331,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2)
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f1329])).

fof(f1329,plain,
    ( spl9_29
  <=> r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f3046,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2)
    | ~ r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_23
    | spl9_59 ),
    inference(subsumption_resolution,[],[f3045,f1043])).

fof(f1043,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f1042])).

fof(f1042,plain,
    ( spl9_23
  <=> m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f3045,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2)
    | ~ r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_59 ),
    inference(subsumption_resolution,[],[f3044,f129])).

fof(f3044,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2)
    | ~ r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_4
    | ~ spl9_5
    | spl9_59 ),
    inference(resolution,[],[f3022,f169])).

fof(f3022,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK5(sK0,sK2,sK1))
    | spl9_59 ),
    inference(avatar_component_clause,[],[f3020])).

fof(f3020,plain,
    ( spl9_59
  <=> r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK5(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f3027,plain,
    ( ~ spl9_59
    | spl9_60
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9
    | ~ spl9_23
    | ~ spl9_45
    | ~ spl9_49 ),
    inference(avatar_split_clause,[],[f2385,f2365,f2106,f1042,f138,f93,f83,f78,f73,f3024,f3020])).

fof(f3024,plain,
    ( spl9_60
  <=> sK5(sK0,sK1,sK2) = sK5(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f73,plain,
    ( spl9_1
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f83,plain,
    ( spl9_3
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f2365,plain,
    ( spl9_49
  <=> sK5(sK0,sK1,sK2) = k10_lattice3(sK0,sK5(sK0,sK2,sK1),sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f2385,plain,
    ( sK5(sK0,sK1,sK2) = sK5(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK5(sK0,sK2,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9
    | ~ spl9_23
    | ~ spl9_45
    | ~ spl9_49 ),
    inference(subsumption_resolution,[],[f2384,f1043])).

fof(f2384,plain,
    ( sK5(sK0,sK1,sK2) = sK5(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK5(sK0,sK2,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9
    | ~ spl9_45
    | ~ spl9_49 ),
    inference(subsumption_resolution,[],[f2376,f2107])).

fof(f2376,plain,
    ( sK5(sK0,sK1,sK2) = sK5(sK0,sK2,sK1)
    | ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK5(sK0,sK2,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9
    | ~ spl9_49 ),
    inference(superposition,[],[f2367,f196])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( k10_lattice3(sK0,X1,X0) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f195,f142])).

fof(f142,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f120,f140])).

fof(f120,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X0) )
    | ~ spl9_1
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f116,f75])).

fof(f75,plain,
    ( v3_orders_2(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X0) )
    | ~ spl9_5 ),
    inference(resolution,[],[f95,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | k10_lattice3(sK0,X1,X0) = X1 )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X0) = X1
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X0) = X1 )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(resolution,[],[f191,f176])).

fof(f176,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,X0,X1) = X2 )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f175,f95])).

fof(f175,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2)
        | r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2))
        | k10_lattice3(sK0,X0,X1) = X2 )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f105,f85])).

fof(f85,plain,
    ( v1_lattice3(sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f105,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2)
        | r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2))
        | k10_lattice3(sK0,X0,X1) = X2 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f97,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f97,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2)
        | r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2))
        | k10_lattice3(sK0,X0,X1) = X2 )
    | ~ spl9_2 ),
    inference(resolution,[],[f80,f51])).

fof(f51,plain,(
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
      | r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f191,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_orders_2(sK0,X8,sK7(sK0,X6,X7,X8))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X6,X8)
        | ~ r1_orders_2(sK0,X7,X8)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k10_lattice3(sK0,X6,X7) = X8 )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f190,f95])).

fof(f190,plain,
    ( ! [X6,X8,X7] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X6,X8)
        | ~ r1_orders_2(sK0,X7,X8)
        | ~ r1_orders_2(sK0,X8,sK7(sK0,X6,X7,X8))
        | k10_lattice3(sK0,X6,X7) = X8 )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f107,f85])).

fof(f107,plain,
    ( ! [X6,X8,X7] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X6,X8)
        | ~ r1_orders_2(sK0,X7,X8)
        | ~ r1_orders_2(sK0,X8,sK7(sK0,X6,X7,X8))
        | k10_lattice3(sK0,X6,X7) = X8 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f99,f37])).

fof(f99,plain,
    ( ! [X6,X8,X7] :
        ( v2_struct_0(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X6,X8)
        | ~ r1_orders_2(sK0,X7,X8)
        | ~ r1_orders_2(sK0,X8,sK7(sK0,X6,X7,X8))
        | k10_lattice3(sK0,X6,X7) = X8 )
    | ~ spl9_2 ),
    inference(resolution,[],[f80,f53])).

fof(f53,plain,(
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
      | ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2367,plain,
    ( sK5(sK0,sK1,sK2) = k10_lattice3(sK0,sK5(sK0,sK2,sK1),sK5(sK0,sK1,sK2))
    | ~ spl9_49 ),
    inference(avatar_component_clause,[],[f2365])).

fof(f2368,plain,
    ( spl9_49
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_9
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f2160,f2102,f138,f127,f122,f93,f88,f83,f78,f73,f2365])).

fof(f2102,plain,
    ( spl9_44
  <=> r1_orders_2(sK0,sK5(sK0,sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f2160,plain,
    ( sK5(sK0,sK1,sK2) = k10_lattice3(sK0,sK5(sK0,sK2,sK1),sK5(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_9
    | ~ spl9_44 ),
    inference(subsumption_resolution,[],[f2156,f124])).

fof(f2156,plain,
    ( sK5(sK0,sK1,sK2) = k10_lattice3(sK0,sK5(sK0,sK2,sK1),sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_9
    | ~ spl9_44 ),
    inference(duplicate_literal_removal,[],[f2150])).

fof(f2150,plain,
    ( sK5(sK0,sK1,sK2) = k10_lattice3(sK0,sK5(sK0,sK2,sK1),sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_9
    | ~ spl9_44 ),
    inference(resolution,[],[f2104,f1177])).

fof(f1177,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X1,sK1),X0)
        | sK5(sK0,sK1,X0) = k10_lattice3(sK0,sK5(sK0,X1,sK1),sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_9 ),
    inference(subsumption_resolution,[],[f1176,f90])).

fof(f1176,plain,
    ( ! [X0,X1] :
        ( sK5(sK0,sK1,X0) = k10_lattice3(sK0,sK5(sK0,X1,sK1),sK5(sK0,sK1,X0))
        | ~ r1_orders_2(sK0,sK5(sK0,X1,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_9 ),
    inference(subsumption_resolution,[],[f1175,f95])).

fof(f1175,plain,
    ( ! [X0,X1] :
        ( sK5(sK0,sK1,X0) = k10_lattice3(sK0,sK5(sK0,X1,sK1),sK5(sK0,sK1,X0))
        | ~ r1_orders_2(sK0,sK5(sK0,X1,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_9 ),
    inference(subsumption_resolution,[],[f1174,f129])).

fof(f1174,plain,
    ( ! [X0,X1] :
        ( sK5(sK0,sK1,X0) = k10_lattice3(sK0,sK5(sK0,X1,sK1),sK5(sK0,sK1,X0))
        | ~ r1_orders_2(sK0,sK5(sK0,X1,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f1171])).

fof(f1171,plain,
    ( ! [X0,X1] :
        ( sK5(sK0,sK1,X0) = k10_lattice3(sK0,sK5(sK0,X1,sK1),sK5(sK0,sK1,X0))
        | ~ r1_orders_2(sK0,sK5(sK0,X1,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_9 ),
    inference(resolution,[],[f785,f44])).

fof(f785,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(sK5(sK0,X7,sK1),u1_struct_0(sK0))
        | sK5(sK0,sK1,X6) = k10_lattice3(sK0,sK5(sK0,X7,sK1),sK5(sK0,sK1,X6))
        | ~ r1_orders_2(sK0,sK5(sK0,X7,sK1),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_9 ),
    inference(subsumption_resolution,[],[f779,f129])).

fof(f779,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | sK5(sK0,sK1,X6) = k10_lattice3(sK0,sK5(sK0,X7,sK1),sK5(sK0,sK1,X6))
        | ~ r1_orders_2(sK0,sK5(sK0,X7,sK1),X6)
        | ~ m1_subset_1(sK5(sK0,X7,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_9 ),
    inference(resolution,[],[f459,f144])).

fof(f459,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(sK0,X3,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,sK1,X2) = k10_lattice3(sK0,X3,sK5(sK0,sK1,X2))
        | ~ r1_orders_2(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_9 ),
    inference(resolution,[],[f345,f129])).

fof(f345,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f344,f90])).

fof(f344,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f343,f95])).

fof(f343,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f342])).

fof(f342,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f217,f44])).

fof(f217,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(sK5(sK0,X8,X9),u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | sK5(sK0,X8,X9) = k10_lattice3(sK0,X10,sK5(sK0,X8,X9))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X10,X8)
        | ~ r1_orders_2(sK0,X10,X9)
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(sK5(sK0,X8,X9),u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | sK5(sK0,X8,X9) = k10_lattice3(sK0,X10,sK5(sK0,X8,X9))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X10,X8)
        | ~ r1_orders_2(sK0,X10,X9)
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f197,f169])).

fof(f197,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(sK0,X3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X2) = X2 )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f194,f142])).

fof(f194,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X2)
        | ~ r1_orders_2(sK0,X2,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X2) = X2 )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X2)
        | ~ r1_orders_2(sK0,X2,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X2) = X2
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X2)
        | ~ r1_orders_2(sK0,X2,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X2) = X2 )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(resolution,[],[f191,f183])).

fof(f183,plain,
    ( ! [X4,X5,X3] :
        ( r1_orders_2(sK0,X4,sK7(sK0,X3,X4,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X5)
        | ~ r1_orders_2(sK0,X4,X5)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X4) = X5 )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f182,f95])).

fof(f182,plain,
    ( ! [X4,X5,X3] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X5)
        | ~ r1_orders_2(sK0,X4,X5)
        | r1_orders_2(sK0,X4,sK7(sK0,X3,X4,X5))
        | k10_lattice3(sK0,X3,X4) = X5 )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f106,f85])).

fof(f106,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X5)
        | ~ r1_orders_2(sK0,X4,X5)
        | r1_orders_2(sK0,X4,sK7(sK0,X3,X4,X5))
        | k10_lattice3(sK0,X3,X4) = X5 )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f98,f37])).

fof(f98,plain,
    ( ! [X4,X5,X3] :
        ( v2_struct_0(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X5)
        | ~ r1_orders_2(sK0,X4,X5)
        | r1_orders_2(sK0,X4,sK7(sK0,X3,X4,X5))
        | k10_lattice3(sK0,X3,X4) = X5 )
    | ~ spl9_2 ),
    inference(resolution,[],[f80,f52])).

fof(f52,plain,(
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
      | r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2104,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK2,sK1),sK2)
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f2102])).

fof(f2176,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_45 ),
    inference(avatar_contradiction_clause,[],[f2175])).

fof(f2175,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_45 ),
    inference(subsumption_resolution,[],[f2174,f90])).

fof(f2174,plain,
    ( ~ v2_lattice3(sK0)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_45 ),
    inference(subsumption_resolution,[],[f2173,f95])).

fof(f2173,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ spl9_6
    | ~ spl9_7
    | spl9_45 ),
    inference(subsumption_resolution,[],[f2172,f129])).

fof(f2172,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ spl9_6
    | spl9_45 ),
    inference(subsumption_resolution,[],[f2171,f124])).

fof(f2171,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | spl9_45 ),
    inference(resolution,[],[f2108,f44])).

fof(f2108,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | spl9_45 ),
    inference(avatar_component_clause,[],[f2106])).

fof(f2139,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_44 ),
    inference(avatar_contradiction_clause,[],[f2138])).

fof(f2138,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_44 ),
    inference(subsumption_resolution,[],[f2137,f124])).

fof(f2137,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | spl9_44 ),
    inference(subsumption_resolution,[],[f2136,f129])).

fof(f2136,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_4
    | ~ spl9_5
    | spl9_44 ),
    inference(resolution,[],[f2103,f143])).

fof(f2103,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,sK2,sK1),sK2)
    | spl9_44 ),
    inference(avatar_component_clause,[],[f2102])).

fof(f2061,plain,
    ( spl9_43
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_9
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f2013,f454,f138,f127,f122,f93,f88,f83,f78,f73,f2058])).

fof(f2058,plain,
    ( spl9_43
  <=> sK2 = k10_lattice3(sK0,sK5(sK0,sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f454,plain,
    ( spl9_18
  <=> sK2 = sK5(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f2013,plain,
    ( sK2 = k10_lattice3(sK0,sK5(sK0,sK2,sK1),sK2)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_9
    | ~ spl9_18 ),
    inference(resolution,[],[f1985,f129])).

fof(f1985,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK2 = k10_lattice3(sK0,sK5(sK0,sK2,X0),sK2) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9
    | ~ spl9_18 ),
    inference(forward_demodulation,[],[f1984,f456])).

fof(f456,plain,
    ( sK2 = sK5(sK0,sK2,sK2)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f454])).

fof(f1984,plain,
    ( ! [X0] :
        ( sK5(sK0,sK2,sK2) = k10_lattice3(sK0,sK5(sK0,sK2,X0),sK5(sK0,sK2,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(subsumption_resolution,[],[f1983,f124])).

fof(f1983,plain,
    ( ! [X0] :
        ( sK5(sK0,sK2,sK2) = k10_lattice3(sK0,sK5(sK0,sK2,X0),sK5(sK0,sK2,sK2))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f1972])).

fof(f1972,plain,
    ( ! [X0] :
        ( sK5(sK0,sK2,sK2) = k10_lattice3(sK0,sK5(sK0,sK2,X0),sK5(sK0,sK2,sK2))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(resolution,[],[f1128,f143])).

fof(f1128,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,sK2,X1),X0)
        | sK5(sK0,sK2,X0) = k10_lattice3(sK0,sK5(sK0,sK2,X1),sK5(sK0,sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(subsumption_resolution,[],[f1127,f90])).

fof(f1127,plain,
    ( ! [X0,X1] :
        ( sK5(sK0,sK2,X0) = k10_lattice3(sK0,sK5(sK0,sK2,X1),sK5(sK0,sK2,X0))
        | ~ r1_orders_2(sK0,sK5(sK0,sK2,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(subsumption_resolution,[],[f1126,f95])).

fof(f1126,plain,
    ( ! [X0,X1] :
        ( sK5(sK0,sK2,X0) = k10_lattice3(sK0,sK5(sK0,sK2,X1),sK5(sK0,sK2,X0))
        | ~ r1_orders_2(sK0,sK5(sK0,sK2,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(subsumption_resolution,[],[f1125,f124])).

fof(f1125,plain,
    ( ! [X0,X1] :
        ( sK5(sK0,sK2,X0) = k10_lattice3(sK0,sK5(sK0,sK2,X1),sK5(sK0,sK2,X0))
        | ~ r1_orders_2(sK0,sK5(sK0,sK2,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f1122])).

fof(f1122,plain,
    ( ! [X0,X1] :
        ( sK5(sK0,sK2,X0) = k10_lattice3(sK0,sK5(sK0,sK2,X1),sK5(sK0,sK2,X0))
        | ~ r1_orders_2(sK0,sK5(sK0,sK2,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(resolution,[],[f764,f44])).

fof(f764,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK5(sK0,sK2,X2),u1_struct_0(sK0))
        | sK5(sK0,sK2,X1) = k10_lattice3(sK0,sK5(sK0,sK2,X2),sK5(sK0,sK2,X1))
        | ~ r1_orders_2(sK0,sK5(sK0,sK2,X2),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(subsumption_resolution,[],[f758,f124])).

fof(f758,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,sK2,X1) = k10_lattice3(sK0,sK5(sK0,sK2,X2),sK5(sK0,sK2,X1))
        | ~ r1_orders_2(sK0,sK5(sK0,sK2,X2),X1)
        | ~ m1_subset_1(sK5(sK0,sK2,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(resolution,[],[f458,f143])).

fof(f458,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X1,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,sK2,X0) = k10_lattice3(sK0,X1,sK5(sK0,sK2,X0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(resolution,[],[f345,f124])).

fof(f1332,plain,
    ( spl9_29
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_23
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f1302,f1245,f1042,f122,f93,f88,f1329])).

fof(f1245,plain,
    ( spl9_28
  <=> sK5(sK0,sK1,sK2) = sK5(sK0,sK2,sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f1302,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2)
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_23
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f1301,f124])).

fof(f1301,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_23
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f1269,f1043])).

fof(f1269,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_28 ),
    inference(superposition,[],[f143,f1247])).

fof(f1247,plain,
    ( sK5(sK0,sK1,sK2) = sK5(sK0,sK2,sK5(sK0,sK1,sK2))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f1245])).

fof(f1248,plain,
    ( spl9_28
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_9 ),
    inference(avatar_split_clause,[],[f1216,f138,f127,f122,f93,f88,f83,f78,f73,f1245])).

fof(f1216,plain,
    ( sK5(sK0,sK1,sK2) = sK5(sK0,sK2,sK5(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_9 ),
    inference(resolution,[],[f964,f129])).

fof(f964,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X2,sK2) = sK5(sK0,sK2,sK5(sK0,X2,sK2)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(subsumption_resolution,[],[f960,f124])).

fof(f960,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X2,sK2) = sK5(sK0,sK2,sK5(sK0,X2,sK2)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f955])).

fof(f955,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X2,sK2) = sK5(sK0,sK2,sK5(sK0,X2,sK2))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(resolution,[],[f935,f144])).

fof(f935,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X1,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X1,sK2) = sK5(sK0,X0,sK5(sK0,X1,sK2)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(resolution,[],[f427,f124])).

fof(f427,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X5,X6),X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | sK5(sK0,X5,X6) = sK5(sK0,X4,sK5(sK0,X5,X6)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f426,f90])).

fof(f426,plain,
    ( ! [X6,X4,X5] :
        ( sK5(sK0,X5,X6) = sK5(sK0,X4,sK5(sK0,X5,X6))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X5,X6),X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f422,f95])).

fof(f422,plain,
    ( ! [X6,X4,X5] :
        ( sK5(sK0,X5,X6) = sK5(sK0,X4,sK5(sK0,X5,X6))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X5,X6),X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f411,f44])).

fof(f411,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = X1
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f410,f142])).

fof(f410,plain,
    ( ! [X0,X1] :
        ( sK5(sK0,X0,X1) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X1,X1) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f409])).

fof(f409,plain,
    ( ! [X0,X1] :
        ( sK5(sK0,X0,X1) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X1,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f393,f169])).

fof(f393,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X1,sK5(sK0,X0,X1))
        | sK5(sK0,X0,X1) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f392,f90])).

fof(f392,plain,
    ( ! [X0,X1] :
        ( sK5(sK0,X0,X1) = X1
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f391,f95])).

fof(f391,plain,
    ( ! [X0,X1] :
        ( sK5(sK0,X0,X1) = X1
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f390])).

fof(f390,plain,
    ( ! [X0,X1] :
        ( sK5(sK0,X0,X1) = X1
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f366,f44])).

fof(f366,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = X1
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f359])).

fof(f359,plain,
    ( ! [X0,X1] :
        ( sK5(sK0,X0,X1) = X1
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(superposition,[],[f196,f237])).

fof(f237,plain,
    ( ! [X0,X1] :
        ( k10_lattice3(sK0,sK5(sK0,X1,X0),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f236,f90])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,sK5(sK0,X1,X0),X0) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(subsumption_resolution,[],[f235,f95])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,sK5(sK0,X1,X0),X0) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f234])).

fof(f234,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,sK5(sK0,X1,X0),X0) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f218,f44])).

fof(f218,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(sK5(sK0,X7,X6),u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k10_lattice3(sK0,sK5(sK0,X7,X6),X6) = X6
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f211])).

fof(f211,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X7,X6),u1_struct_0(sK0))
        | k10_lattice3(sK0,sK5(sK0,X7,X6),X6) = X6
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_9 ),
    inference(resolution,[],[f197,f144])).

fof(f1065,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_23 ),
    inference(avatar_contradiction_clause,[],[f1064])).

fof(f1064,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_23 ),
    inference(subsumption_resolution,[],[f1063,f90])).

fof(f1063,plain,
    ( ~ v2_lattice3(sK0)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_23 ),
    inference(subsumption_resolution,[],[f1062,f95])).

fof(f1062,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ spl9_6
    | ~ spl9_7
    | spl9_23 ),
    inference(subsumption_resolution,[],[f1061,f124])).

fof(f1061,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ spl9_7
    | spl9_23 ),
    inference(subsumption_resolution,[],[f1060,f129])).

fof(f1060,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | spl9_23 ),
    inference(resolution,[],[f1044,f44])).

fof(f1044,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl9_23 ),
    inference(avatar_component_clause,[],[f1042])).

fof(f1049,plain,
    ( ~ spl9_23
    | spl9_24
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f1024,f985,f127,f93,f88,f1046,f1042])).

fof(f985,plain,
    ( spl9_22
  <=> sK5(sK0,sK1,sK2) = sK5(sK0,sK1,sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f1024,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f995,f129])).

fof(f995,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_22 ),
    inference(superposition,[],[f143,f987])).

fof(f987,plain,
    ( sK5(sK0,sK1,sK2) = sK5(sK0,sK1,sK5(sK0,sK1,sK2))
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f985])).

fof(f988,plain,
    ( spl9_22
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_9 ),
    inference(avatar_split_clause,[],[f966,f138,f127,f122,f93,f88,f83,f78,f73,f985])).

fof(f966,plain,
    ( sK5(sK0,sK1,sK2) = sK5(sK0,sK1,sK5(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_9 ),
    inference(resolution,[],[f963,f129])).

fof(f963,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X0,sK2) = sK5(sK0,X0,sK5(sK0,X0,sK2)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(subsumption_resolution,[],[f962,f124])).

fof(f962,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X0,sK2) = sK5(sK0,X0,sK5(sK0,X0,sK2))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f953])).

fof(f953,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X0,sK2) = sK5(sK0,X0,sK5(sK0,X0,sK2))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(resolution,[],[f935,f143])).

fof(f457,plain,
    ( spl9_18
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(avatar_split_clause,[],[f445,f138,f122,f93,f88,f83,f78,f73,f454])).

fof(f445,plain,
    ( sK2 = sK5(sK0,sK2,sK2)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(subsumption_resolution,[],[f444,f124])).

fof(f444,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK2 = sK5(sK0,sK2,sK2)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(duplicate_literal_removal,[],[f440])).

fof(f440,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK2 = sK5(sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(resolution,[],[f418,f142])).

fof(f418,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK2 = sK5(sK0,X0,sK2) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_9 ),
    inference(resolution,[],[f411,f124])).

fof(f189,plain,
    ( ~ spl9_14
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_11 ),
    inference(avatar_split_clause,[],[f168,f154,f127,f122,f93,f88,f78,f186])).

fof(f186,plain,
    ( spl9_14
  <=> sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f154,plain,
    ( spl9_11
  <=> sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f168,plain,
    ( sK2 != k10_lattice3(sK0,k11_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_11 ),
    inference(subsumption_resolution,[],[f167,f129])).

fof(f167,plain,
    ( sK2 != k10_lattice3(sK0,k11_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_11 ),
    inference(subsumption_resolution,[],[f166,f124])).

fof(f166,plain,
    ( sK2 != k10_lattice3(sK0,k11_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_11 ),
    inference(superposition,[],[f156,f159])).

fof(f159,plain,
    ( ! [X21,X20] :
        ( k11_lattice3(sK0,X20,X21) = k12_lattice3(sK0,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | ~ m1_subset_1(X20,u1_struct_0(sK0)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f158,f95])).

fof(f158,plain,
    ( ! [X21,X20] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X20,u1_struct_0(sK0))
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | k11_lattice3(sK0,X20,X21) = k12_lattice3(sK0,X20,X21) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f104,f90])).

fof(f104,plain,
    ( ! [X21,X20] :
        ( ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X20,u1_struct_0(sK0))
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | k11_lattice3(sK0,X20,X21) = k12_lattice3(sK0,X20,X21) )
    | ~ spl9_2 ),
    inference(resolution,[],[f80,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f156,plain,
    ( sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f174,plain,
    ( ~ spl9_12
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_10 ),
    inference(avatar_split_clause,[],[f163,f150,f127,f122,f93,f88,f78,f171])).

fof(f171,plain,
    ( spl9_12
  <=> m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f150,plain,
    ( spl9_10
  <=> m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f163,plain,
    ( ~ m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | spl9_10 ),
    inference(subsumption_resolution,[],[f162,f129])).

fof(f162,plain,
    ( ~ m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | spl9_10 ),
    inference(subsumption_resolution,[],[f160,f124])).

fof(f160,plain,
    ( ~ m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_10 ),
    inference(superposition,[],[f152,f159])).

fof(f152,plain,
    ( ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl9_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f157,plain,
    ( ~ spl9_10
    | ~ spl9_11
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6
    | spl9_8 ),
    inference(avatar_split_clause,[],[f148,f133,f122,f93,f83,f78,f154,f150])).

fof(f133,plain,
    ( spl9_8
  <=> sK2 = k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f148,plain,
    ( sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6
    | spl9_8 ),
    inference(subsumption_resolution,[],[f147,f124])).

fof(f147,plain,
    ( sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | spl9_8 ),
    inference(superposition,[],[f135,f146])).

fof(f146,plain,
    ( ! [X19,X18] :
        ( k10_lattice3(sK0,X18,X19) = k13_lattice3(sK0,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | ~ m1_subset_1(X18,u1_struct_0(sK0)) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f145,f95])).

fof(f145,plain,
    ( ! [X19,X18] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | k10_lattice3(sK0,X18,X19) = k13_lattice3(sK0,X18,X19) )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f103,f85])).

fof(f103,plain,
    ( ! [X19,X18] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | k10_lattice3(sK0,X18,X19) = k13_lattice3(sK0,X18,X19) )
    | ~ spl9_2 ),
    inference(resolution,[],[f80,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f135,plain,
    ( sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | spl9_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f141,plain,
    ( ~ spl9_9
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f131,f93,f83,f138])).

fof(f131,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f111,f95])).

fof(f111,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_struct_0(sK0)
    | ~ spl9_3 ),
    inference(resolution,[],[f85,f37])).

fof(f136,plain,(
    ~ spl9_8 ),
    inference(avatar_split_clause,[],[f30,f133])).

fof(f30,plain,(
    sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
               => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
             => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattice3)).

fof(f130,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f31,f127])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f125,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f29,f122])).

fof(f29,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f96,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f36,f93])).

fof(f36,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f91,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f35,f88])).

fof(f35,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f86,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f34,f83])).

fof(f34,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f81,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f33,f78])).

fof(f33,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f76,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f32,f73])).

fof(f32,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:09:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.38  ipcrm: permission denied for id (1231257604)
% 0.22/0.38  ipcrm: permission denied for id (1231355912)
% 0.22/0.38  ipcrm: permission denied for id (1231421450)
% 0.22/0.39  ipcrm: permission denied for id (1231650834)
% 0.22/0.40  ipcrm: permission denied for id (1231716372)
% 0.22/0.40  ipcrm: permission denied for id (1231749141)
% 0.22/0.41  ipcrm: permission denied for id (1231978524)
% 0.22/0.41  ipcrm: permission denied for id (1232109601)
% 0.22/0.41  ipcrm: permission denied for id (1232175139)
% 0.22/0.42  ipcrm: permission denied for id (1232240677)
% 0.22/0.42  ipcrm: permission denied for id (1232273446)
% 0.22/0.42  ipcrm: permission denied for id (1232371754)
% 0.22/0.42  ipcrm: permission denied for id (1232404523)
% 0.22/0.43  ipcrm: permission denied for id (1232437292)
% 0.22/0.43  ipcrm: permission denied for id (1232633905)
% 0.22/0.43  ipcrm: permission denied for id (1232666674)
% 0.22/0.45  ipcrm: permission denied for id (1232961596)
% 0.22/0.45  ipcrm: permission denied for id (1232994365)
% 0.22/0.45  ipcrm: permission denied for id (1233027134)
% 0.22/0.45  ipcrm: permission denied for id (1233190979)
% 0.22/0.46  ipcrm: permission denied for id (1233256517)
% 0.22/0.46  ipcrm: permission denied for id (1233289286)
% 0.22/0.46  ipcrm: permission denied for id (1233322055)
% 0.22/0.46  ipcrm: permission denied for id (1233354824)
% 0.22/0.46  ipcrm: permission denied for id (1233453131)
% 0.22/0.47  ipcrm: permission denied for id (1233485901)
% 0.22/0.47  ipcrm: permission denied for id (1233551439)
% 0.22/0.47  ipcrm: permission denied for id (1233616977)
% 0.22/0.47  ipcrm: permission denied for id (1233649746)
% 0.22/0.48  ipcrm: permission denied for id (1233911897)
% 0.22/0.49  ipcrm: permission denied for id (1234010205)
% 0.22/0.49  ipcrm: permission denied for id (1234042974)
% 0.22/0.49  ipcrm: permission denied for id (1234075743)
% 0.22/0.49  ipcrm: permission denied for id (1234141281)
% 0.22/0.49  ipcrm: permission denied for id (1234174050)
% 0.22/0.49  ipcrm: permission denied for id (1234272355)
% 0.22/0.50  ipcrm: permission denied for id (1234305125)
% 0.22/0.50  ipcrm: permission denied for id (1234337894)
% 0.22/0.50  ipcrm: permission denied for id (1234370663)
% 0.22/0.50  ipcrm: permission denied for id (1234436200)
% 0.22/0.50  ipcrm: permission denied for id (1234468969)
% 0.22/0.51  ipcrm: permission denied for id (1234567277)
% 0.22/0.51  ipcrm: permission denied for id (1234600046)
% 0.22/0.51  ipcrm: permission denied for id (1234665584)
% 0.22/0.51  ipcrm: permission denied for id (1234731123)
% 0.22/0.52  ipcrm: permission denied for id (1234763894)
% 0.22/0.52  ipcrm: permission denied for id (1234829433)
% 0.22/0.53  ipcrm: permission denied for id (1234927741)
% 0.22/0.53  ipcrm: permission denied for id (1234993279)
% 0.39/0.62  % (21446)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.39/0.63  % (21461)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.39/0.64  % (21453)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.39/0.65  % (21460)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.39/0.65  % (21450)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.39/0.65  % (21445)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.39/0.66  % (21457)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.39/0.66  % (21444)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.39/0.67  % (21454)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.39/0.67  % (21444)Refutation not found, incomplete strategy% (21444)------------------------------
% 0.39/0.67  % (21444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.67  % (21444)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.67  
% 0.39/0.67  % (21444)Memory used [KB]: 10618
% 0.39/0.67  % (21444)Time elapsed: 0.085 s
% 0.39/0.67  % (21444)------------------------------
% 0.39/0.67  % (21444)------------------------------
% 0.39/0.67  % (21448)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.39/0.67  % (21449)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.39/0.68  % (21451)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.39/0.68  % (21443)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.39/0.68  % (21456)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.39/0.68  % (21447)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.39/0.68  % (21455)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.39/0.69  % (21452)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.39/0.69  % (21458)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.39/0.69  % (21463)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.39/0.69  % (21463)Refutation not found, incomplete strategy% (21463)------------------------------
% 0.39/0.69  % (21463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.69  % (21463)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.69  
% 0.39/0.69  % (21463)Memory used [KB]: 10618
% 0.39/0.69  % (21463)Time elapsed: 0.098 s
% 0.39/0.69  % (21463)------------------------------
% 0.39/0.69  % (21463)------------------------------
% 0.39/0.70  % (21462)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.39/0.70  % (21459)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.51/0.99  % (21446)Refutation found. Thanks to Tanya!
% 0.51/0.99  % SZS status Theorem for theBenchmark
% 0.51/0.99  % SZS output start Proof for theBenchmark
% 0.51/0.99  fof(f3586,plain,(
% 0.51/0.99    $false),
% 0.51/0.99    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f96,f125,f130,f136,f141,f157,f174,f189,f457,f988,f1049,f1065,f1248,f1332,f2061,f2139,f2176,f2368,f3027,f3050,f3583,f3584,f3585])).
% 0.51/0.99  fof(f3585,plain,(
% 0.51/0.99    k11_lattice3(sK0,sK1,sK2) != sK5(sK0,sK2,sK1) | sK5(sK0,sK1,sK2) != sK5(sK0,sK2,sK1) | m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))),
% 0.51/0.99    introduced(theory_tautology_sat_conflict,[])).
% 0.51/0.99  fof(f3584,plain,(
% 0.51/0.99    k11_lattice3(sK0,sK1,sK2) != sK5(sK0,sK2,sK1) | sK5(sK0,sK1,sK2) != sK5(sK0,sK2,sK1) | sK2 != k10_lattice3(sK0,sK5(sK0,sK2,sK1),sK2) | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK1,sK2),sK2)),
% 0.51/0.99    introduced(theory_tautology_sat_conflict,[])).
% 0.51/0.99  fof(f3583,plain,(
% 0.51/0.99    spl9_65 | ~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_9 | ~spl9_45),
% 0.51/0.99    inference(avatar_split_clause,[],[f3560,f2106,f138,f127,f122,f93,f88,f78,f3580])).
% 0.51/0.99  fof(f3580,plain,(
% 0.51/0.99    spl9_65 <=> k11_lattice3(sK0,sK1,sK2) = sK5(sK0,sK2,sK1)),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).
% 0.51/0.99  fof(f78,plain,(
% 0.51/0.99    spl9_2 <=> v5_orders_2(sK0)),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.51/0.99  fof(f88,plain,(
% 0.51/0.99    spl9_4 <=> v2_lattice3(sK0)),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.51/0.99  fof(f93,plain,(
% 0.51/0.99    spl9_5 <=> l1_orders_2(sK0)),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.51/0.99  fof(f122,plain,(
% 0.51/0.99    spl9_6 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.51/0.99  fof(f127,plain,(
% 0.51/0.99    spl9_7 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.51/0.99  fof(f138,plain,(
% 0.51/0.99    spl9_9 <=> v2_struct_0(sK0)),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.51/0.99  fof(f2106,plain,(
% 0.51/0.99    spl9_45 <=> m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).
% 0.51/0.99  fof(f3560,plain,(
% 0.51/0.99    k11_lattice3(sK0,sK1,sK2) = sK5(sK0,sK2,sK1) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_9 | ~spl9_45)),
% 0.51/0.99    inference(subsumption_resolution,[],[f3547,f129])).
% 0.51/0.99  fof(f129,plain,(
% 0.51/0.99    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl9_7),
% 0.51/0.99    inference(avatar_component_clause,[],[f127])).
% 0.51/0.99  fof(f3547,plain,(
% 0.51/0.99    ~m1_subset_1(sK1,u1_struct_0(sK0)) | k11_lattice3(sK0,sK1,sK2) = sK5(sK0,sK2,sK1) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9 | ~spl9_45)),
% 0.51/0.99    inference(resolution,[],[f3501,f2107])).
% 0.51/0.99  fof(f2107,plain,(
% 0.51/0.99    m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0)) | ~spl9_45),
% 0.51/0.99    inference(avatar_component_clause,[],[f2106])).
% 0.51/0.99  fof(f3501,plain,(
% 0.51/0.99    ( ! [X0] : (~m1_subset_1(sK5(sK0,sK2,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,X0,sK2) = sK5(sK0,sK2,X0)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f2235,f124])).
% 0.51/0.99  fof(f124,plain,(
% 0.51/0.99    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl9_6),
% 0.51/0.99    inference(avatar_component_clause,[],[f122])).
% 0.51/0.99  fof(f2235,plain,(
% 0.51/0.99    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f2234,f144])).
% 0.51/0.99  fof(f144,plain,(
% 0.51/0.99    ( ! [X6,X5] : (r1_orders_2(sK0,sK5(sK0,X5,X6),X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f114,f95])).
% 0.51/0.99  fof(f95,plain,(
% 0.51/0.99    l1_orders_2(sK0) | ~spl9_5),
% 0.51/0.99    inference(avatar_component_clause,[],[f93])).
% 0.51/0.99  fof(f114,plain,(
% 0.51/0.99    ( ! [X6,X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r1_orders_2(sK0,sK5(sK0,X5,X6),X6) | ~l1_orders_2(sK0)) ) | ~spl9_4),
% 0.51/0.99    inference(resolution,[],[f90,f46])).
% 0.51/0.99  fof(f46,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (~v2_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,sK5(X0,X1,X2),X2) | ~l1_orders_2(X0)) )),
% 0.51/0.99    inference(cnf_transformation,[],[f18])).
% 0.51/0.99  fof(f18,plain,(
% 0.51/0.99    ! [X0] : ((v2_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.51/0.99    inference(flattening,[],[f17])).
% 0.51/0.99  fof(f17,plain,(
% 0.51/0.99    ! [X0] : ((v2_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.51/0.99    inference(ennf_transformation,[],[f4])).
% 0.51/0.99  fof(f4,axiom,(
% 0.51/0.99    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))),
% 0.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattice3)).
% 0.51/0.99  fof(f90,plain,(
% 0.51/0.99    v2_lattice3(sK0) | ~spl9_4),
% 0.51/0.99    inference(avatar_component_clause,[],[f88])).
% 0.51/0.99  fof(f2234,plain,(
% 0.51/0.99    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X3)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f2231,f143])).
% 0.51/0.99  fof(f143,plain,(
% 0.51/0.99    ( ! [X4,X3] : (r1_orders_2(sK0,sK5(sK0,X3,X4),X3) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f113,f95])).
% 0.51/0.99  fof(f113,plain,(
% 0.51/0.99    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_orders_2(sK0,sK5(sK0,X3,X4),X3) | ~l1_orders_2(sK0)) ) | ~spl9_4),
% 0.51/0.99    inference(resolution,[],[f90,f45])).
% 0.51/0.99  fof(f45,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (~v2_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,sK5(X0,X1,X2),X1) | ~l1_orders_2(X0)) )),
% 0.51/0.99    inference(cnf_transformation,[],[f18])).
% 0.51/0.99  fof(f2231,plain,(
% 0.51/0.99    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X3)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f2221])).
% 0.51/0.99  fof(f2221,plain,(
% 0.51/0.99    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X3) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f1327,f223])).
% 0.51/0.99  fof(f223,plain,(
% 0.51/0.99    ( ! [X14,X12,X13] : (r1_orders_2(sK0,sK8(sK0,X12,X13,X14),X13) | ~m1_subset_1(X13,u1_struct_0(sK0)) | ~m1_subset_1(X14,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X14,X12) | ~r1_orders_2(sK0,X14,X13) | ~m1_subset_1(X12,u1_struct_0(sK0)) | k11_lattice3(sK0,X12,X13) = X14) ) | (~spl9_2 | ~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f222,f95])).
% 0.51/0.99  fof(f222,plain,(
% 0.51/0.99    ( ! [X14,X12,X13] : (~l1_orders_2(sK0) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~m1_subset_1(X13,u1_struct_0(sK0)) | ~m1_subset_1(X14,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X14,X12) | ~r1_orders_2(sK0,X14,X13) | r1_orders_2(sK0,sK8(sK0,X12,X13,X14),X13) | k11_lattice3(sK0,X12,X13) = X14) ) | (~spl9_2 | ~spl9_4)),
% 0.51/0.99    inference(subsumption_resolution,[],[f109,f90])).
% 0.51/0.99  fof(f109,plain,(
% 0.51/0.99    ( ! [X14,X12,X13] : (~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~m1_subset_1(X13,u1_struct_0(sK0)) | ~m1_subset_1(X14,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X14,X12) | ~r1_orders_2(sK0,X14,X13) | r1_orders_2(sK0,sK8(sK0,X12,X13,X14),X13) | k11_lattice3(sK0,X12,X13) = X14) ) | ~spl9_2),
% 0.51/0.99    inference(subsumption_resolution,[],[f101,f38])).
% 0.51/0.99  fof(f38,plain,(
% 0.51/0.99    ( ! [X0] : (~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v2_struct_0(X0)) )),
% 0.51/0.99    inference(cnf_transformation,[],[f16])).
% 0.51/0.99  fof(f16,plain,(
% 0.51/0.99    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 0.51/0.99    inference(flattening,[],[f15])).
% 0.51/0.99  fof(f15,plain,(
% 0.51/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.51/0.99    inference(ennf_transformation,[],[f3])).
% 0.51/0.99  fof(f3,axiom,(
% 0.51/0.99    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).
% 0.51/0.99  fof(f101,plain,(
% 0.51/0.99    ( ! [X14,X12,X13] : (v2_struct_0(sK0) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~m1_subset_1(X13,u1_struct_0(sK0)) | ~m1_subset_1(X14,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X14,X12) | ~r1_orders_2(sK0,X14,X13) | r1_orders_2(sK0,sK8(sK0,X12,X13,X14),X13) | k11_lattice3(sK0,X12,X13) = X14) ) | ~spl9_2),
% 0.51/0.99    inference(resolution,[],[f80,f59])).
% 0.51/0.99  fof(f59,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK8(X0,X1,X2,X3),X2) | k11_lattice3(X0,X1,X2) = X3) )),
% 0.51/0.99    inference(cnf_transformation,[],[f24])).
% 0.51/0.99  fof(f24,plain,(
% 0.51/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.51/0.99    inference(flattening,[],[f23])).
% 0.51/0.99  fof(f23,plain,(
% 0.51/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.51/0.99    inference(ennf_transformation,[],[f6])).
% 0.51/0.99  fof(f6,axiom,(
% 0.51/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 0.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).
% 0.51/0.99  fof(f80,plain,(
% 0.51/0.99    v5_orders_2(sK0) | ~spl9_2),
% 0.51/0.99    inference(avatar_component_clause,[],[f78])).
% 0.51/0.99  fof(f1327,plain,(
% 0.51/0.99    ( ! [X2,X3,X1] : (~r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X1,X2)),X1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k11_lattice3(sK0,X2,X3) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f1326,f90])).
% 0.51/0.99  fof(f1326,plain,(
% 0.51/0.99    ( ! [X2,X3,X1] : (sK5(sK0,X1,X2) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X1,X2)),X1) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v2_lattice3(sK0)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f1323,f95])).
% 0.51/0.99  fof(f1323,plain,(
% 0.51/0.99    ( ! [X2,X3,X1] : (sK5(sK0,X1,X2) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X1,X2)),X1) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f1314])).
% 0.51/0.99  fof(f1314,plain,(
% 0.51/0.99    ( ! [X2,X3,X1] : (sK5(sK0,X1,X2) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X1,X2)),X1) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f1039,f44])).
% 0.51/0.99  fof(f44,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0)) )),
% 0.51/0.99    inference(cnf_transformation,[],[f18])).
% 0.51/0.99  fof(f1039,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0)) | sK5(sK0,X1,X0) = k11_lattice3(sK0,X0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X0,X2,sK5(sK0,X1,X0)),X1) | ~r1_orders_2(sK0,sK5(sK0,X1,X0),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f1038,f144])).
% 0.51/0.99  fof(f1038,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X0) = k11_lattice3(sK0,X0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X0,X2,sK5(sK0,X1,X0)),X1) | ~r1_orders_2(sK0,sK5(sK0,X1,X0),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X1,X0),X0) | ~m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f1029])).
% 0.51/0.99  fof(f1029,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X0) = k11_lattice3(sK0,X0,X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X0,X2,sK5(sK0,X1,X0)),X1) | ~r1_orders_2(sK0,sK5(sK0,X1,X0),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X1,X0),X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X1,X0),X0) | ~r1_orders_2(sK0,sK5(sK0,X1,X0),X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X0) = k11_lattice3(sK0,X0,X2)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f701,f199])).
% 0.51/0.99  fof(f199,plain,(
% 0.51/0.99    ( ! [X10,X11,X9] : (r1_orders_2(sK0,sK8(sK0,X9,X10,X11),X9) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X11,X9) | ~r1_orders_2(sK0,X11,X10) | ~m1_subset_1(X9,u1_struct_0(sK0)) | k11_lattice3(sK0,X9,X10) = X11) ) | (~spl9_2 | ~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f198,f95])).
% 0.51/0.99  fof(f198,plain,(
% 0.51/0.99    ( ! [X10,X11,X9] : (~l1_orders_2(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X11,X9) | ~r1_orders_2(sK0,X11,X10) | r1_orders_2(sK0,sK8(sK0,X9,X10,X11),X9) | k11_lattice3(sK0,X9,X10) = X11) ) | (~spl9_2 | ~spl9_4)),
% 0.51/0.99    inference(subsumption_resolution,[],[f108,f90])).
% 0.51/0.99  fof(f108,plain,(
% 0.51/0.99    ( ! [X10,X11,X9] : (~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X11,X9) | ~r1_orders_2(sK0,X11,X10) | r1_orders_2(sK0,sK8(sK0,X9,X10,X11),X9) | k11_lattice3(sK0,X9,X10) = X11) ) | ~spl9_2),
% 0.51/0.99    inference(subsumption_resolution,[],[f100,f38])).
% 0.51/0.99  fof(f100,plain,(
% 0.51/0.99    ( ! [X10,X11,X9] : (v2_struct_0(sK0) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X11,X9) | ~r1_orders_2(sK0,X11,X10) | r1_orders_2(sK0,sK8(sK0,X9,X10,X11),X9) | k11_lattice3(sK0,X9,X10) = X11) ) | ~spl9_2),
% 0.51/0.99    inference(resolution,[],[f80,f58])).
% 0.51/0.99  fof(f58,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK8(X0,X1,X2,X3),X1) | k11_lattice3(X0,X1,X2) = X3) )),
% 0.51/0.99    inference(cnf_transformation,[],[f24])).
% 0.51/0.99  fof(f701,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK8(sK0,X3,X2,sK5(sK0,X0,X1)),X1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X3,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X3,X2,sK5(sK0,X0,X1)),X0) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f700,f90])).
% 0.51/0.99  fof(f700,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X3,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X3,X2,sK5(sK0,X0,X1)),X0) | ~r1_orders_2(sK0,sK8(sK0,X3,X2,sK5(sK0,X0,X1)),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~v2_lattice3(sK0)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f699,f95])).
% 0.51/0.99  fof(f699,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X3,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X3,X2,sK5(sK0,X0,X1)),X0) | ~r1_orders_2(sK0,sK8(sK0,X3,X2,sK5(sK0,X0,X1)),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f694])).
% 0.51/0.99  fof(f694,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X3,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X3,X2,sK5(sK0,X0,X1)),X0) | ~r1_orders_2(sK0,sK8(sK0,X3,X2,sK5(sK0,X0,X1)),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f417,f44])).
% 0.51/0.99  fof(f417,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X2)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f416,f140])).
% 0.51/0.99  fof(f140,plain,(
% 0.51/0.99    ~v2_struct_0(sK0) | spl9_9),
% 0.51/0.99    inference(avatar_component_clause,[],[f138])).
% 0.51/0.99  fof(f416,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f415,f95])).
% 0.51/0.99  fof(f415,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f414,f90])).
% 0.51/0.99  fof(f414,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f413,f80])).
% 0.51/0.99  fof(f413,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f412])).
% 0.51/0.99  fof(f412,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~r1_orders_2(sK0,sK8(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | v2_struct_0(sK0) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(resolution,[],[f287,f57])).
% 0.51/0.99  fof(f57,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | v2_struct_0(X0) | k11_lattice3(X0,X1,X2) = X3) )),
% 0.51/0.99    inference(cnf_transformation,[],[f24])).
% 0.51/0.99  fof(f287,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK8(sK0,X3,X0,sK5(sK0,X1,X2)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X3) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k11_lattice3(sK0,X3,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X3,X0,sK5(sK0,X1,X2)),X1) | ~r1_orders_2(sK0,sK8(sK0,X3,X0,sK5(sK0,X1,X2)),X2) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f286,f90])).
% 0.51/0.99  fof(f286,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X3) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k11_lattice3(sK0,X3,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK8(sK0,X3,X0,sK5(sK0,X1,X2)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X3,X0,sK5(sK0,X1,X2)),X1) | ~r1_orders_2(sK0,sK8(sK0,X3,X0,sK5(sK0,X1,X2)),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_lattice3(sK0)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f285,f95])).
% 0.51/0.99  fof(f285,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X3) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k11_lattice3(sK0,X3,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK8(sK0,X3,X0,sK5(sK0,X1,X2)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X3,X0,sK5(sK0,X1,X2)),X1) | ~r1_orders_2(sK0,sK8(sK0,X3,X0,sK5(sK0,X1,X2)),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f284])).
% 0.51/0.99  fof(f284,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X3) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k11_lattice3(sK0,X3,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK8(sK0,X3,X0,sK5(sK0,X1,X2)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X3,X0,sK5(sK0,X1,X2)),X1) | ~r1_orders_2(sK0,sK8(sK0,X3,X0,sK5(sK0,X1,X2)),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_2 | ~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(resolution,[],[f240,f44])).
% 0.51/0.99  fof(f240,plain,(
% 0.51/0.99    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK5(sK0,X5,X6),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X5,X6),X7) | ~r1_orders_2(sK0,sK5(sK0,X5,X6),X4) | ~m1_subset_1(X7,u1_struct_0(sK0)) | sK5(sK0,X5,X6) = k11_lattice3(sK0,X7,X4) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(sK8(sK0,X7,X4,sK5(sK0,X5,X6)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK8(sK0,X7,X4,sK5(sK0,X5,X6)),X5) | ~r1_orders_2(sK0,sK8(sK0,X7,X4,sK5(sK0,X5,X6)),X6) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(resolution,[],[f233,f169])).
% 0.51/0.99  fof(f169,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (r1_orders_2(sK0,X2,sK5(sK0,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X0) | ~r1_orders_2(sK0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f112,f95])).
% 0.51/0.99  fof(f112,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X0) | ~r1_orders_2(sK0,X2,X1) | r1_orders_2(sK0,X2,sK5(sK0,X0,X1)) | ~l1_orders_2(sK0)) ) | ~spl9_4),
% 0.51/0.99    inference(resolution,[],[f90,f43])).
% 0.51/0.99  fof(f43,plain,(
% 0.51/0.99    ( ! [X4,X2,X0,X1] : (~v2_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_orders_2(X0,X4,X1) | ~r1_orders_2(X0,X4,X2) | r1_orders_2(X0,X4,sK5(X0,X1,X2)) | ~l1_orders_2(X0)) )),
% 0.51/0.99    inference(cnf_transformation,[],[f18])).
% 0.51/0.99  fof(f233,plain,(
% 0.51/0.99    ( ! [X17,X15,X16] : (~r1_orders_2(sK0,sK8(sK0,X15,X16,X17),X17) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~m1_subset_1(X17,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X17,X15) | ~r1_orders_2(sK0,X17,X16) | ~m1_subset_1(X15,u1_struct_0(sK0)) | k11_lattice3(sK0,X15,X16) = X17) ) | (~spl9_2 | ~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f232,f95])).
% 0.51/0.99  fof(f232,plain,(
% 0.51/0.99    ( ! [X17,X15,X16] : (~l1_orders_2(sK0) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~m1_subset_1(X17,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X17,X15) | ~r1_orders_2(sK0,X17,X16) | ~r1_orders_2(sK0,sK8(sK0,X15,X16,X17),X17) | k11_lattice3(sK0,X15,X16) = X17) ) | (~spl9_2 | ~spl9_4)),
% 0.51/0.99    inference(subsumption_resolution,[],[f110,f90])).
% 0.51/0.99  fof(f110,plain,(
% 0.51/0.99    ( ! [X17,X15,X16] : (~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~m1_subset_1(X17,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X17,X15) | ~r1_orders_2(sK0,X17,X16) | ~r1_orders_2(sK0,sK8(sK0,X15,X16,X17),X17) | k11_lattice3(sK0,X15,X16) = X17) ) | ~spl9_2),
% 0.51/0.99    inference(subsumption_resolution,[],[f102,f38])).
% 0.51/0.99  fof(f102,plain,(
% 0.51/0.99    ( ! [X17,X15,X16] : (v2_struct_0(sK0) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~m1_subset_1(X17,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X17,X15) | ~r1_orders_2(sK0,X17,X16) | ~r1_orders_2(sK0,sK8(sK0,X15,X16,X17),X17) | k11_lattice3(sK0,X15,X16) = X17) ) | ~spl9_2),
% 0.51/0.99    inference(resolution,[],[f80,f60])).
% 0.51/0.99  fof(f60,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,sK8(X0,X1,X2,X3),X3) | k11_lattice3(X0,X1,X2) = X3) )),
% 0.51/0.99    inference(cnf_transformation,[],[f24])).
% 0.51/0.99  fof(f3050,plain,(
% 0.51/0.99    ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_23 | ~spl9_24 | ~spl9_29 | spl9_59),
% 0.51/0.99    inference(avatar_contradiction_clause,[],[f3049])).
% 0.51/0.99  fof(f3049,plain,(
% 0.51/0.99    $false | (~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_23 | ~spl9_24 | ~spl9_29 | spl9_59)),
% 0.51/0.99    inference(subsumption_resolution,[],[f3048,f124])).
% 0.51/0.99  fof(f3048,plain,(
% 0.51/0.99    ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_23 | ~spl9_24 | ~spl9_29 | spl9_59)),
% 0.51/0.99    inference(subsumption_resolution,[],[f3047,f1048])).
% 0.51/0.99  fof(f1048,plain,(
% 0.51/0.99    r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK1) | ~spl9_24),
% 0.51/0.99    inference(avatar_component_clause,[],[f1046])).
% 0.51/0.99  fof(f1046,plain,(
% 0.51/0.99    spl9_24 <=> r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK1)),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.51/0.99  fof(f3047,plain,(
% 0.51/0.99    ~r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_23 | ~spl9_29 | spl9_59)),
% 0.51/0.99    inference(subsumption_resolution,[],[f3046,f1331])).
% 0.51/0.99  fof(f1331,plain,(
% 0.51/0.99    r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2) | ~spl9_29),
% 0.51/0.99    inference(avatar_component_clause,[],[f1329])).
% 0.51/0.99  fof(f1329,plain,(
% 0.51/0.99    spl9_29 <=> r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2)),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 0.51/0.99  fof(f3046,plain,(
% 0.51/0.99    ~r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2) | ~r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_23 | spl9_59)),
% 0.51/0.99    inference(subsumption_resolution,[],[f3045,f1043])).
% 0.51/0.99  fof(f1043,plain,(
% 0.51/0.99    m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0)) | ~spl9_23),
% 0.51/0.99    inference(avatar_component_clause,[],[f1042])).
% 0.51/0.99  fof(f1042,plain,(
% 0.51/0.99    spl9_23 <=> m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.51/0.99  fof(f3045,plain,(
% 0.51/0.99    ~m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2) | ~r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_59)),
% 0.51/0.99    inference(subsumption_resolution,[],[f3044,f129])).
% 0.51/0.99  fof(f3044,plain,(
% 0.51/0.99    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2) | ~r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl9_4 | ~spl9_5 | spl9_59)),
% 0.51/0.99    inference(resolution,[],[f3022,f169])).
% 0.51/0.99  fof(f3022,plain,(
% 0.51/0.99    ~r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK5(sK0,sK2,sK1)) | spl9_59),
% 0.51/0.99    inference(avatar_component_clause,[],[f3020])).
% 0.51/0.99  fof(f3020,plain,(
% 0.51/0.99    spl9_59 <=> r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK5(sK0,sK2,sK1))),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).
% 0.51/0.99  fof(f3027,plain,(
% 0.51/0.99    ~spl9_59 | spl9_60 | ~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9 | ~spl9_23 | ~spl9_45 | ~spl9_49),
% 0.51/0.99    inference(avatar_split_clause,[],[f2385,f2365,f2106,f1042,f138,f93,f83,f78,f73,f3024,f3020])).
% 0.51/0.99  fof(f3024,plain,(
% 0.51/0.99    spl9_60 <=> sK5(sK0,sK1,sK2) = sK5(sK0,sK2,sK1)),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).
% 0.51/0.99  fof(f73,plain,(
% 0.51/0.99    spl9_1 <=> v3_orders_2(sK0)),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.51/0.99  fof(f83,plain,(
% 0.51/0.99    spl9_3 <=> v1_lattice3(sK0)),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.51/0.99  fof(f2365,plain,(
% 0.51/0.99    spl9_49 <=> sK5(sK0,sK1,sK2) = k10_lattice3(sK0,sK5(sK0,sK2,sK1),sK5(sK0,sK1,sK2))),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).
% 0.51/0.99  fof(f2385,plain,(
% 0.51/0.99    sK5(sK0,sK1,sK2) = sK5(sK0,sK2,sK1) | ~r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK5(sK0,sK2,sK1)) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9 | ~spl9_23 | ~spl9_45 | ~spl9_49)),
% 0.51/0.99    inference(subsumption_resolution,[],[f2384,f1043])).
% 0.51/0.99  fof(f2384,plain,(
% 0.51/0.99    sK5(sK0,sK1,sK2) = sK5(sK0,sK2,sK1) | ~r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK5(sK0,sK2,sK1)) | ~m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9 | ~spl9_45 | ~spl9_49)),
% 0.51/0.99    inference(subsumption_resolution,[],[f2376,f2107])).
% 0.51/0.99  fof(f2376,plain,(
% 0.51/0.99    sK5(sK0,sK1,sK2) = sK5(sK0,sK2,sK1) | ~m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK5(sK0,sK2,sK1)) | ~m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9 | ~spl9_49)),
% 0.51/0.99    inference(superposition,[],[f2367,f196])).
% 0.51/0.99  fof(f196,plain,(
% 0.51/0.99    ( ! [X0,X1] : (k10_lattice3(sK0,X1,X0) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f195,f142])).
% 0.51/0.99  fof(f142,plain,(
% 0.51/0.99    ( ! [X0] : (r1_orders_2(sK0,X0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f120,f140])).
% 0.51/0.99  fof(f120,plain,(
% 0.51/0.99    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0)) ) | (~spl9_1 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f116,f75])).
% 0.51/0.99  fof(f75,plain,(
% 0.51/0.99    v3_orders_2(sK0) | ~spl9_1),
% 0.51/0.99    inference(avatar_component_clause,[],[f73])).
% 0.51/0.99  fof(f116,plain,(
% 0.51/0.99    ( ! [X0] : (~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0)) ) | ~spl9_5),
% 0.51/0.99    inference(resolution,[],[f95,f49])).
% 0.51/0.99  fof(f49,plain,(
% 0.51/0.99    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1)) )),
% 0.51/0.99    inference(cnf_transformation,[],[f20])).
% 0.51/0.99  fof(f20,plain,(
% 0.51/0.99    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.51/0.99    inference(flattening,[],[f19])).
% 0.51/0.99  fof(f19,plain,(
% 0.51/0.99    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.51/0.99    inference(ennf_transformation,[],[f1])).
% 0.51/0.99  fof(f1,axiom,(
% 0.51/0.99    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 0.51/0.99  fof(f195,plain,(
% 0.51/0.99    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X1) | ~r1_orders_2(sK0,X0,X1) | k10_lattice3(sK0,X1,X0) = X1) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f192])).
% 0.51/0.99  fof(f192,plain,(
% 0.51/0.99    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X1) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X0) = X1 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X1) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X0) = X1) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 0.51/0.99    inference(resolution,[],[f191,f176])).
% 0.51/0.99  fof(f176,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X2) | ~r1_orders_2(sK0,X1,X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,X0,X1) = X2) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f175,f95])).
% 0.51/0.99  fof(f175,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X2) | ~r1_orders_2(sK0,X1,X2) | r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2)) | k10_lattice3(sK0,X0,X1) = X2) ) | (~spl9_2 | ~spl9_3)),
% 0.51/0.99    inference(subsumption_resolution,[],[f105,f85])).
% 0.51/0.99  fof(f85,plain,(
% 0.51/0.99    v1_lattice3(sK0) | ~spl9_3),
% 0.51/0.99    inference(avatar_component_clause,[],[f83])).
% 0.51/0.99  fof(f105,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X2) | ~r1_orders_2(sK0,X1,X2) | r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2)) | k10_lattice3(sK0,X0,X1) = X2) ) | ~spl9_2),
% 0.51/0.99    inference(subsumption_resolution,[],[f97,f37])).
% 0.51/0.99  fof(f37,plain,(
% 0.51/0.99    ( ! [X0] : (~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v2_struct_0(X0)) )),
% 0.51/0.99    inference(cnf_transformation,[],[f14])).
% 0.51/0.99  fof(f14,plain,(
% 0.51/0.99    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.51/0.99    inference(flattening,[],[f13])).
% 0.51/0.99  fof(f13,plain,(
% 0.51/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.51/0.99    inference(ennf_transformation,[],[f2])).
% 0.51/0.99  fof(f2,axiom,(
% 0.51/0.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.51/0.99  fof(f97,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X2) | ~r1_orders_2(sK0,X1,X2) | r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2)) | k10_lattice3(sK0,X0,X1) = X2) ) | ~spl9_2),
% 0.51/0.99    inference(resolution,[],[f80,f51])).
% 0.51/0.99  fof(f51,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,sK7(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3) )),
% 0.51/0.99    inference(cnf_transformation,[],[f22])).
% 0.51/0.99  fof(f22,plain,(
% 0.51/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.51/0.99    inference(flattening,[],[f21])).
% 0.51/0.99  fof(f21,plain,(
% 0.51/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.51/0.99    inference(ennf_transformation,[],[f5])).
% 0.51/0.99  fof(f5,axiom,(
% 0.51/0.99    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).
% 0.51/0.99  fof(f191,plain,(
% 0.51/0.99    ( ! [X6,X8,X7] : (~r1_orders_2(sK0,X8,sK7(sK0,X6,X7,X8)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X6,X8) | ~r1_orders_2(sK0,X7,X8) | ~m1_subset_1(X6,u1_struct_0(sK0)) | k10_lattice3(sK0,X6,X7) = X8) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f190,f95])).
% 0.51/0.99  fof(f190,plain,(
% 0.51/0.99    ( ! [X6,X8,X7] : (~l1_orders_2(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X6,X8) | ~r1_orders_2(sK0,X7,X8) | ~r1_orders_2(sK0,X8,sK7(sK0,X6,X7,X8)) | k10_lattice3(sK0,X6,X7) = X8) ) | (~spl9_2 | ~spl9_3)),
% 0.51/0.99    inference(subsumption_resolution,[],[f107,f85])).
% 0.51/0.99  fof(f107,plain,(
% 0.51/0.99    ( ! [X6,X8,X7] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X6,X8) | ~r1_orders_2(sK0,X7,X8) | ~r1_orders_2(sK0,X8,sK7(sK0,X6,X7,X8)) | k10_lattice3(sK0,X6,X7) = X8) ) | ~spl9_2),
% 0.51/0.99    inference(subsumption_resolution,[],[f99,f37])).
% 0.51/0.99  fof(f99,plain,(
% 0.51/0.99    ( ! [X6,X8,X7] : (v2_struct_0(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X6,X8) | ~r1_orders_2(sK0,X7,X8) | ~r1_orders_2(sK0,X8,sK7(sK0,X6,X7,X8)) | k10_lattice3(sK0,X6,X7) = X8) ) | ~spl9_2),
% 0.51/0.99    inference(resolution,[],[f80,f53])).
% 0.51/0.99  fof(f53,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X3,sK7(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3) )),
% 0.51/0.99    inference(cnf_transformation,[],[f22])).
% 0.51/0.99  fof(f2367,plain,(
% 0.51/0.99    sK5(sK0,sK1,sK2) = k10_lattice3(sK0,sK5(sK0,sK2,sK1),sK5(sK0,sK1,sK2)) | ~spl9_49),
% 0.51/0.99    inference(avatar_component_clause,[],[f2365])).
% 0.51/0.99  fof(f2368,plain,(
% 0.51/0.99    spl9_49 | ~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_9 | ~spl9_44),
% 0.51/0.99    inference(avatar_split_clause,[],[f2160,f2102,f138,f127,f122,f93,f88,f83,f78,f73,f2365])).
% 0.51/0.99  fof(f2102,plain,(
% 0.51/0.99    spl9_44 <=> r1_orders_2(sK0,sK5(sK0,sK2,sK1),sK2)),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).
% 0.51/0.99  fof(f2160,plain,(
% 0.51/0.99    sK5(sK0,sK1,sK2) = k10_lattice3(sK0,sK5(sK0,sK2,sK1),sK5(sK0,sK1,sK2)) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_9 | ~spl9_44)),
% 0.51/0.99    inference(subsumption_resolution,[],[f2156,f124])).
% 0.51/0.99  fof(f2156,plain,(
% 0.51/0.99    sK5(sK0,sK1,sK2) = k10_lattice3(sK0,sK5(sK0,sK2,sK1),sK5(sK0,sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_9 | ~spl9_44)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f2150])).
% 0.51/0.99  fof(f2150,plain,(
% 0.51/0.99    sK5(sK0,sK1,sK2) = k10_lattice3(sK0,sK5(sK0,sK2,sK1),sK5(sK0,sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_9 | ~spl9_44)),
% 0.51/0.99    inference(resolution,[],[f2104,f1177])).
% 0.51/0.99  fof(f1177,plain,(
% 0.51/0.99    ( ! [X0,X1] : (~r1_orders_2(sK0,sK5(sK0,X1,sK1),X0) | sK5(sK0,sK1,X0) = k10_lattice3(sK0,sK5(sK0,X1,sK1),sK5(sK0,sK1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f1176,f90])).
% 0.51/0.99  fof(f1176,plain,(
% 0.51/0.99    ( ! [X0,X1] : (sK5(sK0,sK1,X0) = k10_lattice3(sK0,sK5(sK0,X1,sK1),sK5(sK0,sK1,X0)) | ~r1_orders_2(sK0,sK5(sK0,X1,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f1175,f95])).
% 0.51/0.99  fof(f1175,plain,(
% 0.51/0.99    ( ! [X0,X1] : (sK5(sK0,sK1,X0) = k10_lattice3(sK0,sK5(sK0,X1,sK1),sK5(sK0,sK1,X0)) | ~r1_orders_2(sK0,sK5(sK0,X1,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f1174,f129])).
% 0.51/0.99  fof(f1174,plain,(
% 0.51/0.99    ( ! [X0,X1] : (sK5(sK0,sK1,X0) = k10_lattice3(sK0,sK5(sK0,X1,sK1),sK5(sK0,sK1,X0)) | ~r1_orders_2(sK0,sK5(sK0,X1,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f1171])).
% 0.51/0.99  fof(f1171,plain,(
% 0.51/0.99    ( ! [X0,X1] : (sK5(sK0,sK1,X0) = k10_lattice3(sK0,sK5(sK0,X1,sK1),sK5(sK0,sK1,X0)) | ~r1_orders_2(sK0,sK5(sK0,X1,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f785,f44])).
% 0.51/0.99  fof(f785,plain,(
% 0.51/0.99    ( ! [X6,X7] : (~m1_subset_1(sK5(sK0,X7,sK1),u1_struct_0(sK0)) | sK5(sK0,sK1,X6) = k10_lattice3(sK0,sK5(sK0,X7,sK1),sK5(sK0,sK1,X6)) | ~r1_orders_2(sK0,sK5(sK0,X7,sK1),X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f779,f129])).
% 0.51/0.99  fof(f779,plain,(
% 0.51/0.99    ( ! [X6,X7] : (~m1_subset_1(X6,u1_struct_0(sK0)) | sK5(sK0,sK1,X6) = k10_lattice3(sK0,sK5(sK0,X7,sK1),sK5(sK0,sK1,X6)) | ~r1_orders_2(sK0,sK5(sK0,X7,sK1),X6) | ~m1_subset_1(sK5(sK0,X7,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f459,f144])).
% 0.51/0.99  fof(f459,plain,(
% 0.51/0.99    ( ! [X2,X3] : (~r1_orders_2(sK0,X3,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,sK1,X2) = k10_lattice3(sK0,X3,sK5(sK0,sK1,X2)) | ~r1_orders_2(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f345,f129])).
% 0.51/0.99  fof(f345,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X0,X2) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f344,f90])).
% 0.51/0.99  fof(f344,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f343,f95])).
% 0.51/0.99  fof(f343,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f342])).
% 0.51/0.99  fof(f342,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f217,f44])).
% 0.51/0.99  fof(f217,plain,(
% 0.51/0.99    ( ! [X10,X8,X9] : (~m1_subset_1(sK5(sK0,X8,X9),u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | sK5(sK0,X8,X9) = k10_lattice3(sK0,X10,sK5(sK0,X8,X9)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X10,X8) | ~r1_orders_2(sK0,X10,X9) | ~m1_subset_1(X8,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f212])).
% 0.51/0.99  fof(f212,plain,(
% 0.51/0.99    ( ! [X10,X8,X9] : (~m1_subset_1(sK5(sK0,X8,X9),u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | sK5(sK0,X8,X9) = k10_lattice3(sK0,X10,sK5(sK0,X8,X9)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X10,X8) | ~r1_orders_2(sK0,X10,X9) | ~m1_subset_1(X8,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f197,f169])).
% 0.51/0.99  fof(f197,plain,(
% 0.51/0.99    ( ! [X2,X3] : (~r1_orders_2(sK0,X3,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X2) = X2) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f194,f142])).
% 0.51/0.99  fof(f194,plain,(
% 0.51/0.99    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X2) | ~r1_orders_2(sK0,X2,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X2) = X2) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f193])).
% 0.51/0.99  fof(f193,plain,(
% 0.51/0.99    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X2) | ~r1_orders_2(sK0,X2,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X2) | ~r1_orders_2(sK0,X2,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X2) = X2) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 0.51/0.99    inference(resolution,[],[f191,f183])).
% 0.51/0.99  fof(f183,plain,(
% 0.51/0.99    ( ! [X4,X5,X3] : (r1_orders_2(sK0,X4,sK7(sK0,X3,X4,X5)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X5) | ~r1_orders_2(sK0,X4,X5) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X4) = X5) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f182,f95])).
% 0.51/0.99  fof(f182,plain,(
% 0.51/0.99    ( ! [X4,X5,X3] : (~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X5) | ~r1_orders_2(sK0,X4,X5) | r1_orders_2(sK0,X4,sK7(sK0,X3,X4,X5)) | k10_lattice3(sK0,X3,X4) = X5) ) | (~spl9_2 | ~spl9_3)),
% 0.51/0.99    inference(subsumption_resolution,[],[f106,f85])).
% 0.51/0.99  fof(f106,plain,(
% 0.51/0.99    ( ! [X4,X5,X3] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X5) | ~r1_orders_2(sK0,X4,X5) | r1_orders_2(sK0,X4,sK7(sK0,X3,X4,X5)) | k10_lattice3(sK0,X3,X4) = X5) ) | ~spl9_2),
% 0.51/0.99    inference(subsumption_resolution,[],[f98,f37])).
% 0.51/0.99  fof(f98,plain,(
% 0.51/0.99    ( ! [X4,X5,X3] : (v2_struct_0(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X5) | ~r1_orders_2(sK0,X4,X5) | r1_orders_2(sK0,X4,sK7(sK0,X3,X4,X5)) | k10_lattice3(sK0,X3,X4) = X5) ) | ~spl9_2),
% 0.51/0.99    inference(resolution,[],[f80,f52])).
% 0.51/0.99  fof(f52,plain,(
% 0.51/0.99    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X2,sK7(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3) )),
% 0.51/0.99    inference(cnf_transformation,[],[f22])).
% 0.51/0.99  fof(f2104,plain,(
% 0.51/0.99    r1_orders_2(sK0,sK5(sK0,sK2,sK1),sK2) | ~spl9_44),
% 0.51/0.99    inference(avatar_component_clause,[],[f2102])).
% 0.51/0.99  fof(f2176,plain,(
% 0.51/0.99    ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_45),
% 0.51/0.99    inference(avatar_contradiction_clause,[],[f2175])).
% 0.51/0.99  fof(f2175,plain,(
% 0.51/0.99    $false | (~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_45)),
% 0.51/0.99    inference(subsumption_resolution,[],[f2174,f90])).
% 0.51/0.99  fof(f2174,plain,(
% 0.51/0.99    ~v2_lattice3(sK0) | (~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_45)),
% 0.51/0.99    inference(subsumption_resolution,[],[f2173,f95])).
% 0.51/0.99  fof(f2173,plain,(
% 0.51/0.99    ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | (~spl9_6 | ~spl9_7 | spl9_45)),
% 0.51/0.99    inference(subsumption_resolution,[],[f2172,f129])).
% 0.51/0.99  fof(f2172,plain,(
% 0.51/0.99    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | (~spl9_6 | spl9_45)),
% 0.51/0.99    inference(subsumption_resolution,[],[f2171,f124])).
% 0.51/0.99  fof(f2171,plain,(
% 0.51/0.99    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | spl9_45),
% 0.51/0.99    inference(resolution,[],[f2108,f44])).
% 0.51/0.99  fof(f2108,plain,(
% 0.51/0.99    ~m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0)) | spl9_45),
% 0.51/0.99    inference(avatar_component_clause,[],[f2106])).
% 0.51/0.99  fof(f2139,plain,(
% 0.51/0.99    ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_44),
% 0.51/0.99    inference(avatar_contradiction_clause,[],[f2138])).
% 0.51/0.99  fof(f2138,plain,(
% 0.51/0.99    $false | (~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_44)),
% 0.51/0.99    inference(subsumption_resolution,[],[f2137,f124])).
% 0.51/0.99  fof(f2137,plain,(
% 0.51/0.99    ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl9_4 | ~spl9_5 | ~spl9_7 | spl9_44)),
% 0.51/0.99    inference(subsumption_resolution,[],[f2136,f129])).
% 0.51/0.99  fof(f2136,plain,(
% 0.51/0.99    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl9_4 | ~spl9_5 | spl9_44)),
% 0.51/0.99    inference(resolution,[],[f2103,f143])).
% 0.51/0.99  fof(f2103,plain,(
% 0.51/0.99    ~r1_orders_2(sK0,sK5(sK0,sK2,sK1),sK2) | spl9_44),
% 0.51/0.99    inference(avatar_component_clause,[],[f2102])).
% 0.51/0.99  fof(f2061,plain,(
% 0.51/0.99    spl9_43 | ~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_9 | ~spl9_18),
% 0.51/0.99    inference(avatar_split_clause,[],[f2013,f454,f138,f127,f122,f93,f88,f83,f78,f73,f2058])).
% 0.51/0.99  fof(f2058,plain,(
% 0.51/0.99    spl9_43 <=> sK2 = k10_lattice3(sK0,sK5(sK0,sK2,sK1),sK2)),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 0.51/0.99  fof(f454,plain,(
% 0.51/0.99    spl9_18 <=> sK2 = sK5(sK0,sK2,sK2)),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.51/0.99  fof(f2013,plain,(
% 0.51/0.99    sK2 = k10_lattice3(sK0,sK5(sK0,sK2,sK1),sK2) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_9 | ~spl9_18)),
% 0.51/0.99    inference(resolution,[],[f1985,f129])).
% 0.51/0.99  fof(f1985,plain,(
% 0.51/0.99    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,sK5(sK0,sK2,X0),sK2)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9 | ~spl9_18)),
% 0.51/0.99    inference(forward_demodulation,[],[f1984,f456])).
% 0.51/0.99  fof(f456,plain,(
% 0.51/0.99    sK2 = sK5(sK0,sK2,sK2) | ~spl9_18),
% 0.51/0.99    inference(avatar_component_clause,[],[f454])).
% 0.51/0.99  fof(f1984,plain,(
% 0.51/0.99    ( ! [X0] : (sK5(sK0,sK2,sK2) = k10_lattice3(sK0,sK5(sK0,sK2,X0),sK5(sK0,sK2,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f1983,f124])).
% 0.51/0.99  fof(f1983,plain,(
% 0.51/0.99    ( ! [X0] : (sK5(sK0,sK2,sK2) = k10_lattice3(sK0,sK5(sK0,sK2,X0),sK5(sK0,sK2,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f1972])).
% 0.51/0.99  fof(f1972,plain,(
% 0.51/0.99    ( ! [X0] : (sK5(sK0,sK2,sK2) = k10_lattice3(sK0,sK5(sK0,sK2,X0),sK5(sK0,sK2,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f1128,f143])).
% 0.51/0.99  fof(f1128,plain,(
% 0.51/0.99    ( ! [X0,X1] : (~r1_orders_2(sK0,sK5(sK0,sK2,X1),X0) | sK5(sK0,sK2,X0) = k10_lattice3(sK0,sK5(sK0,sK2,X1),sK5(sK0,sK2,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f1127,f90])).
% 0.51/0.99  fof(f1127,plain,(
% 0.51/0.99    ( ! [X0,X1] : (sK5(sK0,sK2,X0) = k10_lattice3(sK0,sK5(sK0,sK2,X1),sK5(sK0,sK2,X0)) | ~r1_orders_2(sK0,sK5(sK0,sK2,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f1126,f95])).
% 0.51/0.99  fof(f1126,plain,(
% 0.51/0.99    ( ! [X0,X1] : (sK5(sK0,sK2,X0) = k10_lattice3(sK0,sK5(sK0,sK2,X1),sK5(sK0,sK2,X0)) | ~r1_orders_2(sK0,sK5(sK0,sK2,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f1125,f124])).
% 0.51/0.99  fof(f1125,plain,(
% 0.51/0.99    ( ! [X0,X1] : (sK5(sK0,sK2,X0) = k10_lattice3(sK0,sK5(sK0,sK2,X1),sK5(sK0,sK2,X0)) | ~r1_orders_2(sK0,sK5(sK0,sK2,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f1122])).
% 0.51/0.99  fof(f1122,plain,(
% 0.51/0.99    ( ! [X0,X1] : (sK5(sK0,sK2,X0) = k10_lattice3(sK0,sK5(sK0,sK2,X1),sK5(sK0,sK2,X0)) | ~r1_orders_2(sK0,sK5(sK0,sK2,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f764,f44])).
% 0.51/0.99  fof(f764,plain,(
% 0.51/0.99    ( ! [X2,X1] : (~m1_subset_1(sK5(sK0,sK2,X2),u1_struct_0(sK0)) | sK5(sK0,sK2,X1) = k10_lattice3(sK0,sK5(sK0,sK2,X2),sK5(sK0,sK2,X1)) | ~r1_orders_2(sK0,sK5(sK0,sK2,X2),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f758,f124])).
% 0.51/0.99  fof(f758,plain,(
% 0.51/0.99    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,sK2,X1) = k10_lattice3(sK0,sK5(sK0,sK2,X2),sK5(sK0,sK2,X1)) | ~r1_orders_2(sK0,sK5(sK0,sK2,X2),X1) | ~m1_subset_1(sK5(sK0,sK2,X2),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f458,f143])).
% 0.51/0.99  fof(f458,plain,(
% 0.51/0.99    ( ! [X0,X1] : (~r1_orders_2(sK0,X1,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,sK2,X0) = k10_lattice3(sK0,X1,sK5(sK0,sK2,X0)) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f345,f124])).
% 0.51/0.99  fof(f1332,plain,(
% 0.51/0.99    spl9_29 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_23 | ~spl9_28),
% 0.51/0.99    inference(avatar_split_clause,[],[f1302,f1245,f1042,f122,f93,f88,f1329])).
% 0.51/0.99  fof(f1245,plain,(
% 0.51/0.99    spl9_28 <=> sK5(sK0,sK1,sK2) = sK5(sK0,sK2,sK5(sK0,sK1,sK2))),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 0.51/0.99  fof(f1302,plain,(
% 0.51/0.99    r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2) | (~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_23 | ~spl9_28)),
% 0.51/0.99    inference(subsumption_resolution,[],[f1301,f124])).
% 0.51/0.99  fof(f1301,plain,(
% 0.51/0.99    r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl9_4 | ~spl9_5 | ~spl9_23 | ~spl9_28)),
% 0.51/0.99    inference(subsumption_resolution,[],[f1269,f1043])).
% 0.51/0.99  fof(f1269,plain,(
% 0.51/0.99    r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl9_4 | ~spl9_5 | ~spl9_28)),
% 0.51/0.99    inference(superposition,[],[f143,f1247])).
% 0.51/0.99  fof(f1247,plain,(
% 0.51/0.99    sK5(sK0,sK1,sK2) = sK5(sK0,sK2,sK5(sK0,sK1,sK2)) | ~spl9_28),
% 0.51/0.99    inference(avatar_component_clause,[],[f1245])).
% 0.51/0.99  fof(f1248,plain,(
% 0.51/0.99    spl9_28 | ~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_9),
% 0.51/0.99    inference(avatar_split_clause,[],[f1216,f138,f127,f122,f93,f88,f83,f78,f73,f1245])).
% 0.51/0.99  fof(f1216,plain,(
% 0.51/0.99    sK5(sK0,sK1,sK2) = sK5(sK0,sK2,sK5(sK0,sK1,sK2)) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f964,f129])).
% 0.51/0.99  fof(f964,plain,(
% 0.51/0.99    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X2,sK2) = sK5(sK0,sK2,sK5(sK0,X2,sK2))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f960,f124])).
% 0.51/0.99  fof(f960,plain,(
% 0.51/0.99    ( ! [X2] : (~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X2,sK2) = sK5(sK0,sK2,sK5(sK0,X2,sK2))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f955])).
% 0.51/0.99  fof(f955,plain,(
% 0.51/0.99    ( ! [X2] : (~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X2,sK2) = sK5(sK0,sK2,sK5(sK0,X2,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f935,f144])).
% 0.51/0.99  fof(f935,plain,(
% 0.51/0.99    ( ! [X0,X1] : (~r1_orders_2(sK0,sK5(sK0,X1,sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X1,sK2) = sK5(sK0,X0,sK5(sK0,X1,sK2))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f427,f124])).
% 0.51/0.99  fof(f427,plain,(
% 0.51/0.99    ( ! [X6,X4,X5] : (~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X5,X6),X4) | ~m1_subset_1(X5,u1_struct_0(sK0)) | sK5(sK0,X5,X6) = sK5(sK0,X4,sK5(sK0,X5,X6))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f426,f90])).
% 0.51/0.99  fof(f426,plain,(
% 0.51/0.99    ( ! [X6,X4,X5] : (sK5(sK0,X5,X6) = sK5(sK0,X4,sK5(sK0,X5,X6)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X5,X6),X4) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f422,f95])).
% 0.51/0.99  fof(f422,plain,(
% 0.51/0.99    ( ! [X6,X4,X5] : (sK5(sK0,X5,X6) = sK5(sK0,X4,sK5(sK0,X5,X6)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X5,X6),X4) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f411,f44])).
% 0.51/0.99  fof(f411,plain,(
% 0.51/0.99    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = X1 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f410,f142])).
% 0.51/0.99  fof(f410,plain,(
% 0.51/0.99    ( ! [X0,X1] : (sK5(sK0,X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | ~r1_orders_2(sK0,X1,X1)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f409])).
% 0.51/0.99  fof(f409,plain,(
% 0.51/0.99    ( ! [X0,X1] : (sK5(sK0,X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | ~r1_orders_2(sK0,X1,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f393,f169])).
% 0.51/0.99  fof(f393,plain,(
% 0.51/0.99    ( ! [X0,X1] : (~r1_orders_2(sK0,X1,sK5(sK0,X0,X1)) | sK5(sK0,X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f392,f90])).
% 0.51/0.99  fof(f392,plain,(
% 0.51/0.99    ( ! [X0,X1] : (sK5(sK0,X0,X1) = X1 | ~r1_orders_2(sK0,X1,sK5(sK0,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f391,f95])).
% 0.51/0.99  fof(f391,plain,(
% 0.51/0.99    ( ! [X0,X1] : (sK5(sK0,X0,X1) = X1 | ~r1_orders_2(sK0,X1,sK5(sK0,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f390])).
% 0.51/0.99  fof(f390,plain,(
% 0.51/0.99    ( ! [X0,X1] : (sK5(sK0,X0,X1) = X1 | ~r1_orders_2(sK0,X1,sK5(sK0,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f366,f44])).
% 0.51/0.99  fof(f366,plain,(
% 0.51/0.99    ( ! [X0,X1] : (~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | sK5(sK0,X0,X1) = X1 | ~r1_orders_2(sK0,X1,sK5(sK0,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f359])).
% 0.51/0.99  fof(f359,plain,(
% 0.51/0.99    ( ! [X0,X1] : (sK5(sK0,X0,X1) = X1 | ~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK5(sK0,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(superposition,[],[f196,f237])).
% 0.51/0.99  fof(f237,plain,(
% 0.51/0.99    ( ! [X0,X1] : (k10_lattice3(sK0,sK5(sK0,X1,X0),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f236,f90])).
% 0.51/0.99  fof(f236,plain,(
% 0.51/0.99    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,sK5(sK0,X1,X0),X0) = X0 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f235,f95])).
% 0.51/0.99  fof(f235,plain,(
% 0.51/0.99    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,sK5(sK0,X1,X0),X0) = X0 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f234])).
% 0.51/0.99  fof(f234,plain,(
% 0.51/0.99    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,sK5(sK0,X1,X0),X0) = X0 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f218,f44])).
% 0.51/0.99  fof(f218,plain,(
% 0.51/0.99    ( ! [X6,X7] : (~m1_subset_1(sK5(sK0,X7,X6),u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | k10_lattice3(sK0,sK5(sK0,X7,X6),X6) = X6 | ~m1_subset_1(X7,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f211])).
% 0.51/0.99  fof(f211,plain,(
% 0.51/0.99    ( ! [X6,X7] : (~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X7,X6),u1_struct_0(sK0)) | k10_lattice3(sK0,sK5(sK0,X7,X6),X6) = X6 | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f197,f144])).
% 0.51/0.99  fof(f1065,plain,(
% 0.51/0.99    ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_23),
% 0.51/0.99    inference(avatar_contradiction_clause,[],[f1064])).
% 0.51/0.99  fof(f1064,plain,(
% 0.51/0.99    $false | (~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_23)),
% 0.51/0.99    inference(subsumption_resolution,[],[f1063,f90])).
% 0.51/0.99  fof(f1063,plain,(
% 0.51/0.99    ~v2_lattice3(sK0) | (~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_23)),
% 0.51/0.99    inference(subsumption_resolution,[],[f1062,f95])).
% 0.51/0.99  fof(f1062,plain,(
% 0.51/0.99    ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | (~spl9_6 | ~spl9_7 | spl9_23)),
% 0.51/0.99    inference(subsumption_resolution,[],[f1061,f124])).
% 0.51/0.99  fof(f1061,plain,(
% 0.51/0.99    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | (~spl9_7 | spl9_23)),
% 0.51/0.99    inference(subsumption_resolution,[],[f1060,f129])).
% 0.51/0.99  fof(f1060,plain,(
% 0.51/0.99    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | spl9_23),
% 0.51/0.99    inference(resolution,[],[f1044,f44])).
% 0.51/0.99  fof(f1044,plain,(
% 0.51/0.99    ~m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0)) | spl9_23),
% 0.51/0.99    inference(avatar_component_clause,[],[f1042])).
% 0.51/0.99  fof(f1049,plain,(
% 0.51/0.99    ~spl9_23 | spl9_24 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_22),
% 0.51/0.99    inference(avatar_split_clause,[],[f1024,f985,f127,f93,f88,f1046,f1042])).
% 0.51/0.99  fof(f985,plain,(
% 0.51/0.99    spl9_22 <=> sK5(sK0,sK1,sK2) = sK5(sK0,sK1,sK5(sK0,sK1,sK2))),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.51/0.99  fof(f1024,plain,(
% 0.51/0.99    r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_22)),
% 0.51/0.99    inference(subsumption_resolution,[],[f995,f129])).
% 0.51/0.99  fof(f995,plain,(
% 0.51/0.99    r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl9_4 | ~spl9_5 | ~spl9_22)),
% 0.51/0.99    inference(superposition,[],[f143,f987])).
% 0.51/0.99  fof(f987,plain,(
% 0.51/0.99    sK5(sK0,sK1,sK2) = sK5(sK0,sK1,sK5(sK0,sK1,sK2)) | ~spl9_22),
% 0.51/0.99    inference(avatar_component_clause,[],[f985])).
% 0.51/0.99  fof(f988,plain,(
% 0.51/0.99    spl9_22 | ~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_9),
% 0.51/0.99    inference(avatar_split_clause,[],[f966,f138,f127,f122,f93,f88,f83,f78,f73,f985])).
% 0.51/0.99  fof(f966,plain,(
% 0.51/0.99    sK5(sK0,sK1,sK2) = sK5(sK0,sK1,sK5(sK0,sK1,sK2)) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f963,f129])).
% 0.51/0.99  fof(f963,plain,(
% 0.51/0.99    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X0,sK2) = sK5(sK0,X0,sK5(sK0,X0,sK2))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f962,f124])).
% 0.51/0.99  fof(f962,plain,(
% 0.51/0.99    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X0,sK2) = sK5(sK0,X0,sK5(sK0,X0,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f953])).
% 0.51/0.99  fof(f953,plain,(
% 0.51/0.99    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X0,sK2) = sK5(sK0,X0,sK5(sK0,X0,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f935,f143])).
% 0.51/0.99  fof(f457,plain,(
% 0.51/0.99    spl9_18 | ~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9),
% 0.51/0.99    inference(avatar_split_clause,[],[f445,f138,f122,f93,f88,f83,f78,f73,f454])).
% 0.51/0.99  fof(f445,plain,(
% 0.51/0.99    sK2 = sK5(sK0,sK2,sK2) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(subsumption_resolution,[],[f444,f124])).
% 0.51/0.99  fof(f444,plain,(
% 0.51/0.99    ~m1_subset_1(sK2,u1_struct_0(sK0)) | sK2 = sK5(sK0,sK2,sK2) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(duplicate_literal_removal,[],[f440])).
% 0.51/0.99  fof(f440,plain,(
% 0.51/0.99    ~m1_subset_1(sK2,u1_struct_0(sK0)) | sK2 = sK5(sK0,sK2,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f418,f142])).
% 0.51/0.99  fof(f418,plain,(
% 0.51/0.99    ( ! [X0] : (~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK2 = sK5(sK0,X0,sK2)) ) | (~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_9)),
% 0.51/0.99    inference(resolution,[],[f411,f124])).
% 0.51/0.99  fof(f189,plain,(
% 0.51/0.99    ~spl9_14 | ~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_11),
% 0.51/0.99    inference(avatar_split_clause,[],[f168,f154,f127,f122,f93,f88,f78,f186])).
% 0.51/0.99  fof(f186,plain,(
% 0.51/0.99    spl9_14 <=> sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK1,sK2),sK2)),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.51/0.99  fof(f154,plain,(
% 0.51/0.99    spl9_11 <=> sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.51/0.99  fof(f168,plain,(
% 0.51/0.99    sK2 != k10_lattice3(sK0,k11_lattice3(sK0,sK1,sK2),sK2) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_11)),
% 0.51/0.99    inference(subsumption_resolution,[],[f167,f129])).
% 0.51/0.99  fof(f167,plain,(
% 0.51/0.99    sK2 != k10_lattice3(sK0,k11_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_11)),
% 0.51/0.99    inference(subsumption_resolution,[],[f166,f124])).
% 0.51/0.99  fof(f166,plain,(
% 0.51/0.99    sK2 != k10_lattice3(sK0,k11_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_11)),
% 0.51/0.99    inference(superposition,[],[f156,f159])).
% 0.51/0.99  fof(f159,plain,(
% 0.51/0.99    ( ! [X21,X20] : (k11_lattice3(sK0,X20,X21) = k12_lattice3(sK0,X20,X21) | ~m1_subset_1(X21,u1_struct_0(sK0)) | ~m1_subset_1(X20,u1_struct_0(sK0))) ) | (~spl9_2 | ~spl9_4 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f158,f95])).
% 0.51/0.99  fof(f158,plain,(
% 0.51/0.99    ( ! [X21,X20] : (~l1_orders_2(sK0) | ~m1_subset_1(X20,u1_struct_0(sK0)) | ~m1_subset_1(X21,u1_struct_0(sK0)) | k11_lattice3(sK0,X20,X21) = k12_lattice3(sK0,X20,X21)) ) | (~spl9_2 | ~spl9_4)),
% 0.51/0.99    inference(subsumption_resolution,[],[f104,f90])).
% 0.51/0.99  fof(f104,plain,(
% 0.51/0.99    ( ! [X21,X20] : (~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X20,u1_struct_0(sK0)) | ~m1_subset_1(X21,u1_struct_0(sK0)) | k11_lattice3(sK0,X20,X21) = k12_lattice3(sK0,X20,X21)) ) | ~spl9_2),
% 0.51/0.99    inference(resolution,[],[f80,f65])).
% 0.51/0.99  fof(f65,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)) )),
% 0.51/0.99    inference(cnf_transformation,[],[f28])).
% 0.51/0.99  fof(f28,plain,(
% 0.51/0.99    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.51/0.99    inference(flattening,[],[f27])).
% 0.51/0.99  fof(f27,plain,(
% 0.51/0.99    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.51/0.99    inference(ennf_transformation,[],[f7])).
% 0.51/0.99  fof(f7,axiom,(
% 0.51/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 0.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.51/0.99  fof(f156,plain,(
% 0.51/0.99    sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | spl9_11),
% 0.51/0.99    inference(avatar_component_clause,[],[f154])).
% 0.51/0.99  fof(f174,plain,(
% 0.51/0.99    ~spl9_12 | ~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_10),
% 0.51/0.99    inference(avatar_split_clause,[],[f163,f150,f127,f122,f93,f88,f78,f171])).
% 0.51/0.99  fof(f171,plain,(
% 0.51/0.99    spl9_12 <=> m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.51/0.99  fof(f150,plain,(
% 0.51/0.99    spl9_10 <=> m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.51/0.99  fof(f163,plain,(
% 0.51/0.99    ~m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | spl9_10)),
% 0.51/0.99    inference(subsumption_resolution,[],[f162,f129])).
% 0.51/0.99  fof(f162,plain,(
% 0.51/0.99    ~m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_6 | spl9_10)),
% 0.51/0.99    inference(subsumption_resolution,[],[f160,f124])).
% 0.51/0.99  fof(f160,plain,(
% 0.51/0.99    ~m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl9_2 | ~spl9_4 | ~spl9_5 | spl9_10)),
% 0.51/0.99    inference(superposition,[],[f152,f159])).
% 0.51/0.99  fof(f152,plain,(
% 0.51/0.99    ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | spl9_10),
% 0.51/0.99    inference(avatar_component_clause,[],[f150])).
% 0.51/0.99  fof(f157,plain,(
% 0.51/0.99    ~spl9_10 | ~spl9_11 | ~spl9_2 | ~spl9_3 | ~spl9_5 | ~spl9_6 | spl9_8),
% 0.51/0.99    inference(avatar_split_clause,[],[f148,f133,f122,f93,f83,f78,f154,f150])).
% 0.51/0.99  fof(f133,plain,(
% 0.51/0.99    spl9_8 <=> sK2 = k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)),
% 0.51/0.99    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.51/0.99  fof(f148,plain,(
% 0.51/0.99    sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl9_2 | ~spl9_3 | ~spl9_5 | ~spl9_6 | spl9_8)),
% 0.51/0.99    inference(subsumption_resolution,[],[f147,f124])).
% 0.51/0.99  fof(f147,plain,(
% 0.51/0.99    sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl9_2 | ~spl9_3 | ~spl9_5 | spl9_8)),
% 0.51/0.99    inference(superposition,[],[f135,f146])).
% 0.51/0.99  fof(f146,plain,(
% 0.51/0.99    ( ! [X19,X18] : (k10_lattice3(sK0,X18,X19) = k13_lattice3(sK0,X18,X19) | ~m1_subset_1(X19,u1_struct_0(sK0)) | ~m1_subset_1(X18,u1_struct_0(sK0))) ) | (~spl9_2 | ~spl9_3 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f145,f95])).
% 0.51/0.99  fof(f145,plain,(
% 0.51/0.99    ( ! [X19,X18] : (~l1_orders_2(sK0) | ~m1_subset_1(X18,u1_struct_0(sK0)) | ~m1_subset_1(X19,u1_struct_0(sK0)) | k10_lattice3(sK0,X18,X19) = k13_lattice3(sK0,X18,X19)) ) | (~spl9_2 | ~spl9_3)),
% 0.51/0.99    inference(subsumption_resolution,[],[f103,f85])).
% 0.51/0.99  fof(f103,plain,(
% 0.51/0.99    ( ! [X19,X18] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X18,u1_struct_0(sK0)) | ~m1_subset_1(X19,u1_struct_0(sK0)) | k10_lattice3(sK0,X18,X19) = k13_lattice3(sK0,X18,X19)) ) | ~spl9_2),
% 0.51/0.99    inference(resolution,[],[f80,f64])).
% 0.51/0.99  fof(f64,plain,(
% 0.51/0.99    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)) )),
% 0.51/0.99    inference(cnf_transformation,[],[f26])).
% 0.51/0.99  fof(f26,plain,(
% 0.51/0.99    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.51/0.99    inference(flattening,[],[f25])).
% 0.51/0.99  fof(f25,plain,(
% 0.51/0.99    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.51/0.99    inference(ennf_transformation,[],[f8])).
% 0.51/0.99  fof(f8,axiom,(
% 0.51/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 0.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.51/0.99  fof(f135,plain,(
% 0.51/0.99    sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | spl9_8),
% 0.51/0.99    inference(avatar_component_clause,[],[f133])).
% 0.51/0.99  fof(f141,plain,(
% 0.51/0.99    ~spl9_9 | ~spl9_3 | ~spl9_5),
% 0.51/0.99    inference(avatar_split_clause,[],[f131,f93,f83,f138])).
% 0.51/0.99  fof(f131,plain,(
% 0.51/0.99    ~v2_struct_0(sK0) | (~spl9_3 | ~spl9_5)),
% 0.51/0.99    inference(subsumption_resolution,[],[f111,f95])).
% 0.51/0.99  fof(f111,plain,(
% 0.51/0.99    ~l1_orders_2(sK0) | ~v2_struct_0(sK0) | ~spl9_3),
% 0.51/0.99    inference(resolution,[],[f85,f37])).
% 0.51/0.99  fof(f136,plain,(
% 0.51/0.99    ~spl9_8),
% 0.51/0.99    inference(avatar_split_clause,[],[f30,f133])).
% 0.51/0.99  fof(f30,plain,(
% 0.51/0.99    sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)),
% 0.51/0.99    inference(cnf_transformation,[],[f12])).
% 0.51/0.99  fof(f12,plain,(
% 0.51/0.99    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 0.51/0.99    inference(flattening,[],[f11])).
% 0.51/0.99  fof(f11,plain,(
% 0.51/0.99    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 0.51/0.99    inference(ennf_transformation,[],[f10])).
% 0.51/0.99  fof(f10,negated_conjecture,(
% 0.51/0.99    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 0.51/0.99    inference(negated_conjecture,[],[f9])).
% 0.51/0.99  fof(f9,conjecture,(
% 0.51/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 0.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattice3)).
% 0.51/0.99  fof(f130,plain,(
% 0.51/0.99    spl9_7),
% 0.51/0.99    inference(avatar_split_clause,[],[f31,f127])).
% 0.51/0.99  fof(f31,plain,(
% 0.51/0.99    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.51/0.99    inference(cnf_transformation,[],[f12])).
% 0.51/0.99  fof(f125,plain,(
% 0.51/0.99    spl9_6),
% 0.51/0.99    inference(avatar_split_clause,[],[f29,f122])).
% 0.51/0.99  fof(f29,plain,(
% 0.51/0.99    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.51/0.99    inference(cnf_transformation,[],[f12])).
% 0.51/0.99  fof(f96,plain,(
% 0.51/0.99    spl9_5),
% 0.51/0.99    inference(avatar_split_clause,[],[f36,f93])).
% 0.51/0.99  fof(f36,plain,(
% 0.51/0.99    l1_orders_2(sK0)),
% 0.51/0.99    inference(cnf_transformation,[],[f12])).
% 0.51/0.99  fof(f91,plain,(
% 0.51/0.99    spl9_4),
% 0.51/0.99    inference(avatar_split_clause,[],[f35,f88])).
% 0.51/0.99  fof(f35,plain,(
% 0.51/0.99    v2_lattice3(sK0)),
% 0.51/0.99    inference(cnf_transformation,[],[f12])).
% 0.51/0.99  fof(f86,plain,(
% 0.51/0.99    spl9_3),
% 0.51/0.99    inference(avatar_split_clause,[],[f34,f83])).
% 0.51/0.99  fof(f34,plain,(
% 0.51/0.99    v1_lattice3(sK0)),
% 0.51/0.99    inference(cnf_transformation,[],[f12])).
% 0.51/0.99  fof(f81,plain,(
% 0.51/0.99    spl9_2),
% 0.51/0.99    inference(avatar_split_clause,[],[f33,f78])).
% 0.51/0.99  fof(f33,plain,(
% 0.51/0.99    v5_orders_2(sK0)),
% 0.51/0.99    inference(cnf_transformation,[],[f12])).
% 0.51/0.99  fof(f76,plain,(
% 0.51/0.99    spl9_1),
% 0.51/0.99    inference(avatar_split_clause,[],[f32,f73])).
% 0.51/0.99  fof(f32,plain,(
% 0.51/0.99    v3_orders_2(sK0)),
% 0.51/0.99    inference(cnf_transformation,[],[f12])).
% 0.51/0.99  % SZS output end Proof for theBenchmark
% 0.51/0.99  % (21446)------------------------------
% 0.51/0.99  % (21446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.51/0.99  % (21446)Termination reason: Refutation
% 0.51/0.99  
% 0.51/0.99  % (21446)Memory used [KB]: 13688
% 0.51/0.99  % (21446)Time elapsed: 0.416 s
% 0.51/0.99  % (21446)------------------------------
% 0.51/0.99  % (21446)------------------------------
% 0.51/0.99  % (21304)Success in time 0.627 s
%------------------------------------------------------------------------------
