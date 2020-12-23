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
% DateTime   : Thu Dec  3 13:22:59 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  283 ( 588 expanded)
%              Number of leaves         :   72 ( 279 expanded)
%              Depth                    :   13
%              Number of atoms          : 1708 (3567 expanded)
%              Number of equality atoms :   80 ( 148 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2284,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f136,f140,f144,f148,f152,f156,f160,f164,f179,f185,f329,f334,f339,f427,f494,f522,f525,f567,f609,f644,f649,f656,f662,f668,f674,f1083,f1150,f1160,f1272,f1499,f1632,f1663,f1668,f1695,f1700,f1860,f2183,f2195,f2234,f2235,f2236,f2243,f2251,f2281,f2283])).

fof(f2283,plain,
    ( sK1 != k11_lattice3(sK0,sK1,sK1)
    | sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) = k11_lattice3(sK0,sK1,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2281,plain,
    ( sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | r1_orders_2(sK0,sK3(sK0,sK1,sK1,sK1),sK1)
    | ~ r1_orders_2(sK0,sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2251,plain,
    ( ~ spl8_177
    | ~ spl8_336
    | spl8_337
    | ~ spl8_3
    | ~ spl8_193 ),
    inference(avatar_split_clause,[],[f1364,f1270,f138,f2249,f2246,f1158])).

fof(f1158,plain,
    ( spl8_177
  <=> r1_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_177])])).

fof(f2246,plain,
    ( spl8_336
  <=> r1_orders_2(sK0,sK3(sK0,sK1,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_336])])).

fof(f2249,plain,
    ( spl8_337
  <=> sK1 = k11_lattice3(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_337])])).

fof(f138,plain,
    ( spl8_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f1270,plain,
    ( spl8_193
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,sK3(sK0,X0,X1,X2),X2)
        | k11_lattice3(sK0,X0,X1) = X2
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_193])])).

fof(f1364,plain,
    ( sK1 = k11_lattice3(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK3(sK0,sK1,sK1,sK1),sK1)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ spl8_3
    | ~ spl8_193 ),
    inference(resolution,[],[f1328,f139])).

fof(f139,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f138])).

fof(f1328,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK0))
        | k11_lattice3(sK0,sK1,sK1) = X8
        | ~ r1_orders_2(sK0,sK3(sK0,sK1,sK1,X8),X8)
        | ~ r1_orders_2(sK0,X8,sK1) )
    | ~ spl8_3
    | ~ spl8_193 ),
    inference(duplicate_literal_removal,[],[f1321])).

fof(f1321,plain,
    ( ! [X8] :
        ( ~ r1_orders_2(sK0,sK3(sK0,sK1,sK1,X8),X8)
        | k11_lattice3(sK0,sK1,sK1) = X8
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X8,sK1)
        | ~ r1_orders_2(sK0,X8,sK1) )
    | ~ spl8_3
    | ~ spl8_193 ),
    inference(resolution,[],[f1279,f139])).

fof(f1279,plain,
    ( ! [X12,X11] :
        ( ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1,X11,X12),X12)
        | k11_lattice3(sK0,sK1,X11) = X12
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X12,sK1)
        | ~ r1_orders_2(sK0,X12,X11) )
    | ~ spl8_3
    | ~ spl8_193 ),
    inference(resolution,[],[f1271,f139])).

fof(f1271,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = X2
        | ~ r1_orders_2(sK0,sK3(sK0,X0,X1,X2),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X2,X1) )
    | ~ spl8_193 ),
    inference(avatar_component_clause,[],[f1270])).

fof(f2243,plain,
    ( spl8_55
    | ~ spl8_54
    | ~ spl8_3
    | ~ spl8_37
    | ~ spl8_56 ),
    inference(avatar_split_clause,[],[f530,f438,f332,f138,f432,f435])).

fof(f435,plain,
    ( spl8_55
  <=> sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f432,plain,
    ( spl8_54
  <=> r1_orders_2(sK0,sK1,sK7(sK0,sK1,k5_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f332,plain,
    ( spl8_37
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,X0,sK7(sK0,X0,X1))
        | k1_yellow_0(sK0,X1) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f438,plain,
    ( spl8_56
  <=> r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f530,plain,
    ( ~ r1_orders_2(sK0,sK1,sK7(sK0,sK1,k5_waybel_0(sK0,sK1)))
    | sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | ~ spl8_3
    | ~ spl8_37
    | ~ spl8_56 ),
    inference(resolution,[],[f439,f343])).

fof(f343,plain,
    ( ! [X8] :
        ( ~ r2_lattice3(sK0,X8,sK1)
        | ~ r1_orders_2(sK0,sK1,sK7(sK0,sK1,X8))
        | sK1 = k1_yellow_0(sK0,X8) )
    | ~ spl8_3
    | ~ spl8_37 ),
    inference(resolution,[],[f333,f139])).

fof(f333,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_yellow_0(sK0,X1) = X0
        | ~ r1_orders_2(sK0,X0,sK7(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X1,X0) )
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f332])).

fof(f439,plain,
    ( r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1)
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f438])).

fof(f2236,plain,
    ( sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | r2_hidden(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k5_waybel_0(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))))
    | ~ r2_hidden(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k5_waybel_0(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2235,plain,
    ( sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | r1_orders_2(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),sK1)
    | ~ r1_orders_2(sK0,sK1,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2234,plain,
    ( spl8_39
    | ~ spl8_7
    | ~ spl8_5
    | ~ spl8_4
    | ~ spl8_3
    | spl8_328 ),
    inference(avatar_split_clause,[],[f2223,f2181,f138,f142,f146,f154,f350])).

fof(f350,plain,
    ( spl8_39
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f154,plain,
    ( spl8_7
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f146,plain,
    ( spl8_5
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f142,plain,
    ( spl8_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f2181,plain,
    ( spl8_328
  <=> r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_328])])).

fof(f2223,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_328 ),
    inference(duplicate_literal_removal,[],[f2222])).

fof(f2222,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_328 ),
    inference(resolution,[],[f2182,f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f124,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f57])).

fof(f57,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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

fof(f2182,plain,
    ( ~ r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK1),sK1)
    | spl8_328 ),
    inference(avatar_component_clause,[],[f2181])).

fof(f2195,plain,
    ( sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) != k11_lattice3(sK0,sK1,sK1)
    | v4_waybel_7(sK1,sK0)
    | ~ v4_waybel_7(k11_lattice3(sK0,sK1,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2183,plain,
    ( ~ spl8_328
    | ~ spl8_3
    | spl8_177
    | ~ spl8_284 ),
    inference(avatar_split_clause,[],[f2175,f1858,f1158,f138,f2181])).

fof(f1858,plain,
    ( spl8_284
  <=> ! [X1,X0] :
        ( r1_orders_2(sK0,X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK1)
        | r1_orders_2(sK0,X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_284])])).

fof(f2175,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK1),sK1)
    | spl8_177
    | ~ spl8_284 ),
    inference(resolution,[],[f2160,f1159])).

fof(f1159,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | spl8_177 ),
    inference(avatar_component_clause,[],[f1158])).

fof(f2160,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X0),sK1) )
    | ~ spl8_284 ),
    inference(duplicate_literal_removal,[],[f2159])).

fof(f2159,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X0),sK1) )
    | ~ spl8_284 ),
    inference(factoring,[],[f1859])).

fof(f1859,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK1)
        | r1_orders_2(sK0,X1,sK1) )
    | ~ spl8_284 ),
    inference(avatar_component_clause,[],[f1858])).

fof(f1860,plain,
    ( ~ spl8_3
    | spl8_284
    | ~ spl8_2
    | ~ spl8_264 ),
    inference(avatar_split_clause,[],[f1845,f1666,f134,f1858,f138])).

fof(f134,plain,
    ( spl8_2
  <=> v5_waybel_6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1666,plain,
    ( spl8_264
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),X2)
        | r1_orders_2(sK0,X0,X2)
        | r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v5_waybel_6(X2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_264])])).

fof(f1845,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,sK1)
        | r1_orders_2(sK0,X1,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_264 ),
    inference(resolution,[],[f1667,f135])).

fof(f135,plain,
    ( v5_waybel_6(sK1,sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f134])).

fof(f1667,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_waybel_6(X2,sK0)
        | r1_orders_2(sK0,X0,X2)
        | r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_264 ),
    inference(avatar_component_clause,[],[f1666])).

fof(f1700,plain,
    ( ~ spl8_237
    | ~ spl8_80
    | ~ spl8_3
    | spl8_220
    | ~ spl8_166
    | spl8_226 ),
    inference(avatar_split_clause,[],[f1502,f1457,f1081,f1421,f138,f601,f1504])).

fof(f1504,plain,
    ( spl8_237
  <=> r1_orders_2(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_237])])).

fof(f601,plain,
    ( spl8_80
  <=> m1_subset_1(k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f1421,plain,
    ( spl8_220
  <=> k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) = k11_lattice3(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_220])])).

fof(f1081,plain,
    ( spl8_166
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(sK3(sK0,X0,X1,X2),u1_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = X2
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_166])])).

fof(f1457,plain,
    ( spl8_226
  <=> m1_subset_1(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_226])])).

fof(f1502,plain,
    ( k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) = k11_lattice3(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),sK1)
    | ~ spl8_166
    | spl8_226 ),
    inference(duplicate_literal_removal,[],[f1500])).

fof(f1500,plain,
    ( k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) = k11_lattice3(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),sK1)
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),sK1)
    | ~ spl8_166
    | spl8_226 ),
    inference(resolution,[],[f1458,f1082])).

fof(f1082,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK3(sK0,X0,X1,X2),u1_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = X2
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X2,X1) )
    | ~ spl8_166 ),
    inference(avatar_component_clause,[],[f1081])).

fof(f1458,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),u1_struct_0(sK0))
    | spl8_226 ),
    inference(avatar_component_clause,[],[f1457])).

fof(f1695,plain,
    ( spl8_39
    | ~ spl8_7
    | ~ spl8_5
    | ~ spl8_4
    | ~ spl8_3
    | ~ spl8_80
    | ~ spl8_237
    | spl8_220
    | spl8_263 ),
    inference(avatar_split_clause,[],[f1676,f1661,f1421,f1504,f601,f138,f142,f146,f154,f350])).

fof(f1661,plain,
    ( spl8_263
  <=> r1_orders_2(sK0,sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_263])])).

fof(f1676,plain,
    ( k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) = k11_lattice3(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),sK1)
    | ~ m1_subset_1(k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_263 ),
    inference(duplicate_literal_removal,[],[f1675])).

fof(f1675,plain,
    ( k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) = k11_lattice3(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),sK1)
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),sK1)
    | ~ m1_subset_1(k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_263 ),
    inference(resolution,[],[f1662,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
      | k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1662,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),sK1)
    | spl8_263 ),
    inference(avatar_component_clause,[],[f1661])).

fof(f1668,plain,
    ( ~ spl8_4
    | spl8_264
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f1664,f146,f1666,f142])).

fof(f1664,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_waybel_6(X2,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_orders_2(sK0,X1,X2)
        | r1_orders_2(sK0,X0,X2) )
    | ~ spl8_5 ),
    inference(resolution,[],[f726,f147])).

fof(f147,plain,
    ( v2_lattice3(sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f146])).

fof(f726,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_lattice3(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X3,X2)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f725])).

fof(f725,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X3,X2)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f92,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f92,plain,(
    ! [X4,X0,X5,X1] :
      ( v2_struct_0(X0)
      | r1_orders_2(X0,X4,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X5,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_6(X1,X0)
              | ( ~ r1_orders_2(X0,sK5(X0,X1),X1)
                & ~ r1_orders_2(X0,sK4(X0,X1),X1)
                & r1_orders_2(X0,k11_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X1)
                      | r1_orders_2(X0,X4,X1)
                      | ~ r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v5_waybel_6(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f60,f62,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X3,X1)
              & ~ r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r1_orders_2(X0,X3,X1)
            & ~ r1_orders_2(X0,sK4(X0,X1),X1)
            & r1_orders_2(X0,k11_lattice3(X0,sK4(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & ~ r1_orders_2(X0,sK4(X0,X1),X1)
          & r1_orders_2(X0,k11_lattice3(X0,sK4(X0,X1),X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1),X1)
        & ~ r1_orders_2(X0,sK4(X0,X1),X1)
        & r1_orders_2(X0,k11_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_6(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X1)
                      & ~ r1_orders_2(X0,X2,X1)
                      & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X1)
                      | r1_orders_2(X0,X4,X1)
                      | ~ r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v5_waybel_6(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_6(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X1)
                      & ~ r1_orders_2(X0,X2,X1)
                      & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r1_orders_2(X0,X3,X1)
                      | r1_orders_2(X0,X2,X1)
                      | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v5_waybel_6(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_waybel_6(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | r1_orders_2(X0,X2,X1)
                    | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_waybel_6(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | r1_orders_2(X0,X2,X1)
                    | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r1_orders_2(X0,X3,X1)
                        & ~ r1_orders_2(X0,X2,X1)
                        & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_6)).

fof(f1663,plain,
    ( spl8_39
    | ~ spl8_4
    | ~ spl8_3
    | ~ spl8_226
    | ~ spl8_263
    | spl8_229 ),
    inference(avatar_split_clause,[],[f1659,f1468,f1661,f1457,f138,f142,f350])).

fof(f1468,plain,
    ( spl8_229
  <=> r2_hidden(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k5_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_229])])).

fof(f1659,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),sK1)
    | ~ m1_subset_1(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_229 ),
    inference(resolution,[],[f1469,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_0)).

fof(f1469,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k5_waybel_0(sK0,sK1))
    | spl8_229 ),
    inference(avatar_component_clause,[],[f1468])).

fof(f1632,plain,
    ( ~ spl8_3
    | ~ spl8_2
    | spl8_256
    | ~ spl8_92
    | ~ spl8_220 ),
    inference(avatar_split_clause,[],[f1570,f1421,f672,f1630,f134,f138])).

fof(f1630,plain,
    ( spl8_256
  <=> v4_waybel_7(k11_lattice3(sK0,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_256])])).

fof(f672,plain,
    ( spl8_92
  <=> ! [X0] :
        ( ~ v5_waybel_6(X0,sK0)
        | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f1570,plain,
    ( v4_waybel_7(k11_lattice3(sK0,sK1,sK1),sK0)
    | ~ v5_waybel_6(sK1,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_92
    | ~ spl8_220 ),
    inference(superposition,[],[f673,f1422])).

fof(f1422,plain,
    ( k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) = k11_lattice3(sK0,sK1,sK1)
    | ~ spl8_220 ),
    inference(avatar_component_clause,[],[f1421])).

fof(f673,plain,
    ( ! [X0] :
        ( v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)
        | ~ v5_waybel_6(X0,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_92 ),
    inference(avatar_component_clause,[],[f672])).

fof(f1499,plain,
    ( ~ spl8_80
    | ~ spl8_226
    | ~ spl8_236
    | ~ spl8_10
    | spl8_219 ),
    inference(avatar_split_clause,[],[f1455,f1418,f177,f1497,f1457,f601])).

fof(f1497,plain,
    ( spl8_236
  <=> r2_hidden(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k5_waybel_0(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_236])])).

fof(f177,plain,
    ( spl8_10
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k5_waybel_0(sK0,X1))
        | r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f1418,plain,
    ( spl8_219
  <=> r1_orders_2(sK0,sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_219])])).

fof(f1455,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k5_waybel_0(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))))
    | ~ m1_subset_1(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl8_10
    | spl8_219 ),
    inference(resolution,[],[f1419,f178])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,k5_waybel_0(sK0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f177])).

fof(f1419,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)))
    | spl8_219 ),
    inference(avatar_component_clause,[],[f1418])).

fof(f1272,plain,
    ( spl8_39
    | ~ spl8_5
    | ~ spl8_4
    | spl8_193
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f1268,f154,f1270,f142,f146,f350])).

fof(f1268,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,sK3(sK0,X0,X1,X2),X2)
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | k11_lattice3(sK0,X0,X1) = X2
        | v2_struct_0(sK0) )
    | ~ spl8_7 ),
    inference(resolution,[],[f91,f155])).

fof(f155,plain,
    ( v5_orders_2(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | k11_lattice3(X0,X1,X2) = X3
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1160,plain,
    ( spl8_39
    | ~ spl8_4
    | ~ spl8_3
    | ~ spl8_177
    | spl8_61 ),
    inference(avatar_split_clause,[],[f1156,f468,f1158,f138,f142,f350])).

fof(f468,plain,
    ( spl8_61
  <=> r2_hidden(sK1,k5_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).

fof(f1156,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_61 ),
    inference(duplicate_literal_removal,[],[f1155])).

fof(f1155,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_61 ),
    inference(resolution,[],[f469,f99])).

fof(f469,plain,
    ( ~ r2_hidden(sK1,k5_waybel_0(sK0,sK1))
    | spl8_61 ),
    inference(avatar_component_clause,[],[f468])).

fof(f1150,plain,
    ( ~ spl8_56
    | ~ spl8_61
    | ~ spl8_3
    | spl8_55
    | ~ spl8_59
    | ~ spl8_38
    | spl8_54 ),
    inference(avatar_split_clause,[],[f1149,f432,f337,f460,f435,f138,f468,f438])).

fof(f460,plain,
    ( spl8_59
  <=> m1_subset_1(sK7(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f337,plain,
    ( spl8_38
  <=> ! [X1,X0,X2] :
        ( k1_yellow_0(sK0,X0) = X1
        | ~ m1_subset_1(sK7(sK0,X1,X0),u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK7(sK0,X1,X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,X0)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f1149,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k5_waybel_0(sK0,sK1))
    | ~ r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1)
    | ~ spl8_38
    | spl8_54 ),
    inference(duplicate_literal_removal,[],[f1146])).

fof(f1146,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k5_waybel_0(sK0,sK1))
    | ~ r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_38
    | spl8_54 ),
    inference(resolution,[],[f338,f433])).

fof(f433,plain,
    ( ~ r1_orders_2(sK0,sK1,sK7(sK0,sK1,k5_waybel_0(sK0,sK1)))
    | spl8_54 ),
    inference(avatar_component_clause,[],[f432])).

fof(f338,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X2,sK7(sK0,X1,X0))
        | ~ m1_subset_1(sK7(sK0,X1,X0),u1_struct_0(sK0))
        | k1_yellow_0(sK0,X0) = X1
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,X0)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f337])).

fof(f1083,plain,
    ( spl8_39
    | ~ spl8_5
    | ~ spl8_4
    | spl8_166
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f1079,f154,f1081,f142,f146,f350])).

fof(f1079,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK3(sK0,X0,X1,X2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | k11_lattice3(sK0,X0,X1) = X2
        | v2_struct_0(sK0) )
    | ~ spl8_7 ),
    inference(resolution,[],[f88,f155])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | k11_lattice3(X0,X1,X2) = X3
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f674,plain,
    ( spl8_39
    | ~ spl8_8
    | ~ spl8_4
    | spl8_92
    | ~ spl8_91 ),
    inference(avatar_split_clause,[],[f670,f666,f672,f142,f158,f350])).

fof(f158,plain,
    ( spl8_8
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f666,plain,
    ( spl8_91
  <=> ! [X0] :
        ( v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)
        | ~ v5_waybel_6(X0,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v12_waybel_0(k5_waybel_0(sK0,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).

fof(f670,plain,
    ( ! [X0] :
        ( ~ v5_waybel_6(X0,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_91 ),
    inference(duplicate_literal_removal,[],[f669])).

fof(f669,plain,
    ( ! [X0] :
        ( ~ v5_waybel_6(X0,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_91 ),
    inference(resolution,[],[f667,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v12_waybel_0(k5_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_waybel_0)).

fof(f667,plain,
    ( ! [X0] :
        ( ~ v12_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | ~ v5_waybel_6(X0,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) )
    | ~ spl8_91 ),
    inference(avatar_component_clause,[],[f666])).

fof(f668,plain,
    ( spl8_39
    | ~ spl8_9
    | ~ spl8_4
    | spl8_91
    | ~ spl8_90 ),
    inference(avatar_split_clause,[],[f664,f660,f666,f142,f162,f350])).

fof(f162,plain,
    ( spl8_9
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f660,plain,
    ( spl8_90
  <=> ! [X0] :
        ( ~ v5_waybel_6(X0,sK0)
        | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)
        | ~ v12_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k5_waybel_0(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_90])])).

fof(f664,plain,
    ( ! [X0] :
        ( v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)
        | ~ v12_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_waybel_6(X0,sK0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_90 ),
    inference(duplicate_literal_removal,[],[f663])).

fof(f663,plain,
    ( ! [X0] :
        ( v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)
        | ~ v12_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_waybel_6(X0,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_90 ),
    inference(resolution,[],[f661,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_waybel_0)).

fof(f661,plain,
    ( ! [X0] :
        ( v1_xboole_0(k5_waybel_0(sK0,X0))
        | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)
        | ~ v12_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_waybel_6(X0,sK0) )
    | ~ spl8_90 ),
    inference(avatar_component_clause,[],[f660])).

fof(f662,plain,
    ( spl8_39
    | ~ spl8_9
    | ~ spl8_4
    | spl8_90
    | ~ spl8_89 ),
    inference(avatar_split_clause,[],[f658,f654,f660,f142,f162,f350])).

fof(f654,plain,
    ( spl8_89
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_waybel_6(X0,sK0)
        | v1_xboole_0(k5_waybel_0(sK0,X0))
        | ~ v1_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | ~ v12_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).

fof(f658,plain,
    ( ! [X0] :
        ( ~ v5_waybel_6(X0,sK0)
        | v1_xboole_0(k5_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v12_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_89 ),
    inference(duplicate_literal_removal,[],[f657])).

fof(f657,plain,
    ( ! [X0] :
        ( ~ v5_waybel_6(X0,sK0)
        | v1_xboole_0(k5_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v12_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_89 ),
    inference(resolution,[],[f655,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f655,plain,
    ( ! [X0] :
        ( ~ v1_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | ~ v5_waybel_6(X0,sK0)
        | v1_xboole_0(k5_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v12_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) )
    | ~ spl8_89 ),
    inference(avatar_component_clause,[],[f654])).

fof(f656,plain,
    ( ~ spl8_9
    | ~ spl8_8
    | ~ spl8_7
    | ~ spl8_6
    | ~ spl8_5
    | ~ spl8_4
    | spl8_89
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f651,f647,f654,f142,f146,f150,f154,f158,f162])).

fof(f150,plain,
    ( spl8_6
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f647,plain,
    ( spl8_88
  <=> ! [X0] :
        ( v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_waybel_7(k5_waybel_0(sK0,X0),sK0)
        | ~ v12_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | ~ v1_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | v1_xboole_0(k5_waybel_0(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f651,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)
        | ~ v12_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | ~ v1_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | v1_xboole_0(k5_waybel_0(sK0,X0))
        | ~ v5_waybel_6(X0,sK0)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl8_88 ),
    inference(duplicate_literal_removal,[],[f650])).

fof(f650,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)
        | ~ v12_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | ~ v1_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | v1_xboole_0(k5_waybel_0(sK0,X0))
        | ~ v5_waybel_6(X0,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl8_88 ),
    inference(resolution,[],[f648,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v1_waybel_7(k5_waybel_0(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_7)).

fof(f648,plain,
    ( ! [X0] :
        ( ~ v1_waybel_7(k5_waybel_0(sK0,X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)
        | ~ v12_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | ~ v1_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | v1_xboole_0(k5_waybel_0(sK0,X0)) )
    | ~ spl8_88 ),
    inference(avatar_component_clause,[],[f647])).

fof(f649,plain,
    ( spl8_39
    | ~ spl8_4
    | spl8_88
    | ~ spl8_87 ),
    inference(avatar_split_clause,[],[f645,f642,f647,f142,f350])).

fof(f642,plain,
    ( spl8_87
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_waybel_7(k1_yellow_0(sK0,X0),sK0)
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK0)
        | ~ v12_waybel_0(X0,sK0)
        | ~ v1_waybel_7(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f645,plain,
    ( ! [X0] :
        ( v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)
        | v1_xboole_0(k5_waybel_0(sK0,X0))
        | ~ v1_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | ~ v12_waybel_0(k5_waybel_0(sK0,X0),sK0)
        | ~ v1_waybel_7(k5_waybel_0(sK0,X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_87 ),
    inference(resolution,[],[f643,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(f643,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_waybel_7(k1_yellow_0(sK0,X0),sK0)
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK0)
        | ~ v12_waybel_0(X0,sK0)
        | ~ v1_waybel_7(X0,sK0) )
    | ~ spl8_87 ),
    inference(avatar_component_clause,[],[f642])).

fof(f644,plain,
    ( ~ spl8_9
    | ~ spl8_8
    | ~ spl8_7
    | ~ spl8_5
    | ~ spl8_4
    | spl8_87
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f638,f150,f642,f142,f146,f154,f158,f162])).

fof(f638,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_7(X0,sK0)
        | ~ v12_waybel_0(X0,sK0)
        | ~ v1_waybel_0(X0,sK0)
        | v1_xboole_0(X0)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | v4_waybel_7(k1_yellow_0(sK0,X0),sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f167,f151])).

fof(f151,plain,
    ( v1_lattice3(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f167,plain,(
    ! [X2,X0] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | v4_waybel_7(k1_yellow_0(X0,X2),X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f126,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f126,plain,(
    ! [X2,X0] :
      ( v4_waybel_7(k1_yellow_0(X0,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( v4_waybel_7(X1,X0)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ( k1_yellow_0(X0,sK6(X0,X1)) = X1
                & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(sK6(X0,X1),X0)
                & v12_waybel_0(sK6(X0,X1),X0)
                & v1_waybel_0(sK6(X0,X1),X0)
                & ~ v1_xboole_0(sK6(X0,X1)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f66,f67])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_yellow_0(X0,X3) = X1
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_7(X3,X0)
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( k1_yellow_0(X0,sK6(X0,X1)) = X1
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_7(sK6(X0,X1),X0)
        & v12_waybel_0(sK6(X0,X1),X0)
        & v1_waybel_0(sK6(X0,X1),X0)
        & ~ v1_xboole_0(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ? [X3] :
                  ( k1_yellow_0(X0,X3) = X1
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X3,X0)
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ? [X2] :
                  ( k1_yellow_0(X0,X2) = X1
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X2,X0)
                  & v12_waybel_0(X2,X0)
                  & v1_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_7)).

fof(f609,plain,
    ( ~ spl8_4
    | spl8_80 ),
    inference(avatar_split_clause,[],[f607,f601,f142])).

fof(f607,plain,
    ( ~ l1_orders_2(sK0)
    | spl8_80 ),
    inference(resolution,[],[f602,f116])).

fof(f602,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | spl8_80 ),
    inference(avatar_component_clause,[],[f601])).

fof(f567,plain,
    ( ~ spl8_4
    | ~ spl8_3
    | spl8_56
    | spl8_72 ),
    inference(avatar_split_clause,[],[f565,f520,f438,f138,f142])).

fof(f520,plain,
    ( spl8_72
  <=> r2_hidden(sK2(sK0,k5_waybel_0(sK0,sK1),sK1),k5_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f565,plain,
    ( r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl8_72 ),
    inference(resolution,[],[f521,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f521,plain,
    ( ~ r2_hidden(sK2(sK0,k5_waybel_0(sK0,sK1),sK1),k5_waybel_0(sK0,sK1))
    | spl8_72 ),
    inference(avatar_component_clause,[],[f520])).

fof(f525,plain,
    ( ~ spl8_4
    | ~ spl8_3
    | spl8_56
    | spl8_68 ),
    inference(avatar_split_clause,[],[f523,f505,f438,f138,f142])).

fof(f505,plain,
    ( spl8_68
  <=> m1_subset_1(sK2(sK0,k5_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f523,plain,
    ( r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl8_68 ),
    inference(resolution,[],[f506,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f506,plain,
    ( ~ m1_subset_1(sK2(sK0,k5_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | spl8_68 ),
    inference(avatar_component_clause,[],[f505])).

fof(f522,plain,
    ( ~ spl8_68
    | ~ spl8_3
    | ~ spl8_72
    | ~ spl8_11
    | spl8_56 ),
    inference(avatar_split_clause,[],[f503,f438,f183,f520,f138,f505])).

fof(f183,plain,
    ( spl8_11
  <=> ! [X1,X0] :
        ( ~ r2_hidden(sK2(sK0,X0,X1),k5_waybel_0(sK0,X1))
        | r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f503,plain,
    ( ~ r2_hidden(sK2(sK0,k5_waybel_0(sK0,sK1),sK1),k5_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,k5_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ spl8_11
    | spl8_56 ),
    inference(resolution,[],[f452,f184])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,X0,X1)
        | ~ r2_hidden(sK2(sK0,X0,X1),k5_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f183])).

fof(f452,plain,
    ( ~ r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1)
    | spl8_56 ),
    inference(avatar_component_clause,[],[f438])).

fof(f494,plain,
    ( ~ spl8_7
    | ~ spl8_4
    | ~ spl8_3
    | ~ spl8_56
    | spl8_55
    | spl8_59 ),
    inference(avatar_split_clause,[],[f491,f460,f435,f438,f138,f142,f154])).

fof(f491,plain,
    ( sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | ~ r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl8_59 ),
    inference(resolution,[],[f461,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X2) = X1
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK7(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK7(X0,X1,X2))
                  & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f69])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK7(X0,X1,X2))
        & r2_lattice3(X0,X2,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f461,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | spl8_59 ),
    inference(avatar_component_clause,[],[f460])).

fof(f427,plain,
    ( ~ spl8_4
    | ~ spl8_5
    | ~ spl8_39 ),
    inference(avatar_split_clause,[],[f425,f350,f146,f142])).

fof(f425,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl8_39 ),
    inference(resolution,[],[f351,f80])).

fof(f351,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f350])).

fof(f339,plain,
    ( ~ spl8_4
    | spl8_38
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f335,f327,f337,f142])).

fof(f327,plain,
    ( spl8_36
  <=> ! [X1,X0] :
        ( r2_lattice3(sK0,X0,sK7(sK0,X1,X0))
        | k1_yellow_0(sK0,X0) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f335,plain,
    ( ! [X2,X0,X1] :
        ( k1_yellow_0(sK0,X0) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK7(sK0,X1,X0))
        | ~ m1_subset_1(sK7(sK0,X1,X0),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_36 ),
    inference(resolution,[],[f328,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f328,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,X0,sK7(sK0,X1,X0))
        | k1_yellow_0(sK0,X0) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1) )
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f327])).

fof(f334,plain,
    ( ~ spl8_4
    | spl8_37
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f330,f154,f332,f142])).

fof(f330,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK7(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | k1_yellow_0(sK0,X1) = X0 )
    | ~ spl8_7 ),
    inference(resolution,[],[f112,f155])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X1,sK7(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f329,plain,
    ( ~ spl8_4
    | spl8_36
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f325,f154,f327,f142])).

fof(f325,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,X0,sK7(sK0,X1,X0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | k1_yellow_0(sK0,X0) = X1 )
    | ~ spl8_7 ),
    inference(resolution,[],[f111,f155])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | r2_lattice3(X0,X2,sK7(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f185,plain,
    ( ~ spl8_4
    | spl8_11
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f181,f177,f183,f142])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(sK0,X0,X1),k5_waybel_0(sK0,X1))
        | ~ m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_10 ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(sK0,X0,X1),k5_waybel_0(sK0,X1))
        | ~ m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_10 ),
    inference(resolution,[],[f178,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f179,plain,
    ( ~ spl8_4
    | spl8_10
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f174,f146,f177,f142])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,k5_waybel_0(sK0,X1)) )
    | ~ spl8_5 ),
    inference(resolution,[],[f173,f147])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | r1_orders_2(X1,X0,X2)
      | ~ r2_hidden(X0,k5_waybel_0(X1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_waybel_0(X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | r1_orders_2(X1,X0,X2)
      | ~ v2_lattice3(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f98,f80])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f164,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f71,f162])).

fof(f71,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ v4_waybel_7(sK1,sK0)
    & v5_waybel_6(sK1,sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v4_waybel_7(X1,X0)
            & v5_waybel_6(X1,X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v4_waybel_7(X1,sK0)
          & v5_waybel_6(X1,sK0)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ~ v4_waybel_7(X1,sK0)
        & v5_waybel_6(X1,sK0)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v4_waybel_7(sK1,sK0)
      & v5_waybel_6(sK1,sK0)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v5_waybel_6(X1,X0)
             => v4_waybel_7(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v4_waybel_7(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_7)).

fof(f160,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f72,f158])).

fof(f72,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f156,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f73,f154])).

fof(f73,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f152,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f74,f150])).

fof(f74,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f148,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f75,f146])).

fof(f75,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f144,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f76,f142])).

fof(f76,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f140,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f77,f138])).

fof(f77,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f136,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f78,f134])).

fof(f78,plain,(
    v5_waybel_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f132,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f79,f130])).

fof(f130,plain,
    ( spl8_1
  <=> v4_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f79,plain,(
    ~ v4_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:47:36 EST 2020
% 0.20/0.36  % CPUTime    : 
% 0.22/0.50  % (8190)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (8179)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (8182)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (8186)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (8188)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (8187)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (8178)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.52  % (8180)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.52  % (8194)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (8175)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (8194)Refutation not found, incomplete strategy% (8194)------------------------------
% 0.22/0.52  % (8194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8194)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (8194)Memory used [KB]: 10618
% 0.22/0.52  % (8194)Time elapsed: 0.092 s
% 0.22/0.52  % (8194)------------------------------
% 0.22/0.52  % (8194)------------------------------
% 0.22/0.52  % (8185)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (8174)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (8176)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.53  % (8177)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (8183)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.53  % (8181)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.53  % (8184)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.54  % (8175)Refutation not found, incomplete strategy% (8175)------------------------------
% 0.22/0.54  % (8175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8175)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8175)Memory used [KB]: 10618
% 0.22/0.54  % (8175)Time elapsed: 0.097 s
% 0.22/0.54  % (8175)------------------------------
% 0.22/0.54  % (8175)------------------------------
% 0.22/0.54  % (8192)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.54  % (8193)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.55  % (8189)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.40/0.55  % (8191)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 2.03/0.63  % (8180)Refutation found. Thanks to Tanya!
% 2.03/0.63  % SZS status Theorem for theBenchmark
% 2.03/0.64  % SZS output start Proof for theBenchmark
% 2.03/0.64  fof(f2284,plain,(
% 2.03/0.64    $false),
% 2.03/0.64    inference(avatar_sat_refutation,[],[f132,f136,f140,f144,f148,f152,f156,f160,f164,f179,f185,f329,f334,f339,f427,f494,f522,f525,f567,f609,f644,f649,f656,f662,f668,f674,f1083,f1150,f1160,f1272,f1499,f1632,f1663,f1668,f1695,f1700,f1860,f2183,f2195,f2234,f2235,f2236,f2243,f2251,f2281,f2283])).
% 2.03/0.64  fof(f2283,plain,(
% 2.03/0.64    sK1 != k11_lattice3(sK0,sK1,sK1) | sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) = k11_lattice3(sK0,sK1,sK1)),
% 2.03/0.64    introduced(theory_tautology_sat_conflict,[])).
% 2.03/0.64  fof(f2281,plain,(
% 2.03/0.64    sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | r1_orders_2(sK0,sK3(sK0,sK1,sK1,sK1),sK1) | ~r1_orders_2(sK0,sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)))),
% 2.03/0.64    introduced(theory_tautology_sat_conflict,[])).
% 2.03/0.64  fof(f2251,plain,(
% 2.03/0.64    ~spl8_177 | ~spl8_336 | spl8_337 | ~spl8_3 | ~spl8_193),
% 2.03/0.64    inference(avatar_split_clause,[],[f1364,f1270,f138,f2249,f2246,f1158])).
% 2.03/0.64  fof(f1158,plain,(
% 2.03/0.64    spl8_177 <=> r1_orders_2(sK0,sK1,sK1)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_177])])).
% 2.03/0.64  fof(f2246,plain,(
% 2.03/0.64    spl8_336 <=> r1_orders_2(sK0,sK3(sK0,sK1,sK1,sK1),sK1)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_336])])).
% 2.03/0.64  fof(f2249,plain,(
% 2.03/0.64    spl8_337 <=> sK1 = k11_lattice3(sK0,sK1,sK1)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_337])])).
% 2.03/0.64  fof(f138,plain,(
% 2.03/0.64    spl8_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 2.03/0.64  fof(f1270,plain,(
% 2.03/0.64    spl8_193 <=> ! [X1,X0,X2] : (~r1_orders_2(sK0,sK3(sK0,X0,X1,X2),X2) | k11_lattice3(sK0,X0,X1) = X2 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X0) | ~r1_orders_2(sK0,X2,X1))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_193])])).
% 2.03/0.64  fof(f1364,plain,(
% 2.03/0.64    sK1 = k11_lattice3(sK0,sK1,sK1) | ~r1_orders_2(sK0,sK3(sK0,sK1,sK1,sK1),sK1) | ~r1_orders_2(sK0,sK1,sK1) | (~spl8_3 | ~spl8_193)),
% 2.03/0.64    inference(resolution,[],[f1328,f139])).
% 2.03/0.64  fof(f139,plain,(
% 2.03/0.64    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_3),
% 2.03/0.64    inference(avatar_component_clause,[],[f138])).
% 2.03/0.64  fof(f1328,plain,(
% 2.03/0.64    ( ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK0)) | k11_lattice3(sK0,sK1,sK1) = X8 | ~r1_orders_2(sK0,sK3(sK0,sK1,sK1,X8),X8) | ~r1_orders_2(sK0,X8,sK1)) ) | (~spl8_3 | ~spl8_193)),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f1321])).
% 2.03/0.64  fof(f1321,plain,(
% 2.03/0.64    ( ! [X8] : (~r1_orders_2(sK0,sK3(sK0,sK1,sK1,X8),X8) | k11_lattice3(sK0,sK1,sK1) = X8 | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X8,sK1) | ~r1_orders_2(sK0,X8,sK1)) ) | (~spl8_3 | ~spl8_193)),
% 2.03/0.64    inference(resolution,[],[f1279,f139])).
% 2.03/0.64  fof(f1279,plain,(
% 2.03/0.64    ( ! [X12,X11] : (~m1_subset_1(X11,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK3(sK0,sK1,X11,X12),X12) | k11_lattice3(sK0,sK1,X11) = X12 | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X12,sK1) | ~r1_orders_2(sK0,X12,X11)) ) | (~spl8_3 | ~spl8_193)),
% 2.03/0.64    inference(resolution,[],[f1271,f139])).
% 2.03/0.64  fof(f1271,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = X2 | ~r1_orders_2(sK0,sK3(sK0,X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X0) | ~r1_orders_2(sK0,X2,X1)) ) | ~spl8_193),
% 2.03/0.64    inference(avatar_component_clause,[],[f1270])).
% 2.03/0.64  fof(f2243,plain,(
% 2.03/0.64    spl8_55 | ~spl8_54 | ~spl8_3 | ~spl8_37 | ~spl8_56),
% 2.03/0.64    inference(avatar_split_clause,[],[f530,f438,f332,f138,f432,f435])).
% 2.03/0.64  fof(f435,plain,(
% 2.03/0.64    spl8_55 <=> sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).
% 2.03/0.64  fof(f432,plain,(
% 2.03/0.64    spl8_54 <=> r1_orders_2(sK0,sK1,sK7(sK0,sK1,k5_waybel_0(sK0,sK1)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).
% 2.03/0.64  fof(f332,plain,(
% 2.03/0.64    spl8_37 <=> ! [X1,X0] : (~r1_orders_2(sK0,X0,sK7(sK0,X0,X1)) | k1_yellow_0(sK0,X1) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X1,X0))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 2.03/0.64  fof(f438,plain,(
% 2.03/0.64    spl8_56 <=> r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).
% 2.03/0.64  fof(f530,plain,(
% 2.03/0.64    ~r1_orders_2(sK0,sK1,sK7(sK0,sK1,k5_waybel_0(sK0,sK1))) | sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | (~spl8_3 | ~spl8_37 | ~spl8_56)),
% 2.03/0.64    inference(resolution,[],[f439,f343])).
% 2.03/0.64  fof(f343,plain,(
% 2.03/0.64    ( ! [X8] : (~r2_lattice3(sK0,X8,sK1) | ~r1_orders_2(sK0,sK1,sK7(sK0,sK1,X8)) | sK1 = k1_yellow_0(sK0,X8)) ) | (~spl8_3 | ~spl8_37)),
% 2.03/0.64    inference(resolution,[],[f333,f139])).
% 2.03/0.64  fof(f333,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow_0(sK0,X1) = X0 | ~r1_orders_2(sK0,X0,sK7(sK0,X0,X1)) | ~r2_lattice3(sK0,X1,X0)) ) | ~spl8_37),
% 2.03/0.64    inference(avatar_component_clause,[],[f332])).
% 2.03/0.64  fof(f439,plain,(
% 2.03/0.64    r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1) | ~spl8_56),
% 2.03/0.64    inference(avatar_component_clause,[],[f438])).
% 2.03/0.64  fof(f2236,plain,(
% 2.03/0.64    sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | r2_hidden(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k5_waybel_0(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)))) | ~r2_hidden(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k5_waybel_0(sK0,sK1))),
% 2.03/0.64    introduced(theory_tautology_sat_conflict,[])).
% 2.03/0.64  fof(f2235,plain,(
% 2.03/0.64    sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | r1_orders_2(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),sK1) | ~r1_orders_2(sK0,sK1,sK1)),
% 2.03/0.64    introduced(theory_tautology_sat_conflict,[])).
% 2.03/0.64  fof(f2234,plain,(
% 2.03/0.64    spl8_39 | ~spl8_7 | ~spl8_5 | ~spl8_4 | ~spl8_3 | spl8_328),
% 2.03/0.64    inference(avatar_split_clause,[],[f2223,f2181,f138,f142,f146,f154,f350])).
% 2.03/0.64  fof(f350,plain,(
% 2.03/0.64    spl8_39 <=> v2_struct_0(sK0)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 2.03/0.64  fof(f154,plain,(
% 2.03/0.64    spl8_7 <=> v5_orders_2(sK0)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 2.03/0.64  fof(f146,plain,(
% 2.03/0.64    spl8_5 <=> v2_lattice3(sK0)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 2.03/0.64  fof(f142,plain,(
% 2.03/0.64    spl8_4 <=> l1_orders_2(sK0)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 2.03/0.64  fof(f2181,plain,(
% 2.03/0.64    spl8_328 <=> r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK1),sK1)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_328])])).
% 2.03/0.64  fof(f2223,plain,(
% 2.03/0.64    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | spl8_328),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f2222])).
% 2.03/0.64  fof(f2222,plain,(
% 2.03/0.64    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | spl8_328),
% 2.03/0.64    inference(resolution,[],[f2182,f169])).
% 2.03/0.64  fof(f169,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.03/0.64    inference(subsumption_resolution,[],[f124,f121])).
% 2.03/0.64  fof(f121,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f44])).
% 2.03/0.64  fof(f44,plain,(
% 2.03/0.64    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.03/0.64    inference(flattening,[],[f43])).
% 2.03/0.64  fof(f43,plain,(
% 2.03/0.64    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f4])).
% 2.03/0.64  fof(f4,axiom,(
% 2.03/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).
% 2.03/0.64  fof(f124,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.03/0.64    inference(equality_resolution,[],[f86])).
% 2.03/0.64  fof(f86,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f58])).
% 2.03/0.64  fof(f58,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f57])).
% 2.03/0.64  fof(f57,plain,(
% 2.03/0.64    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f56,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(rectify,[],[f55])).
% 2.03/0.64  fof(f55,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(flattening,[],[f54])).
% 2.03/0.64  fof(f54,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(nnf_transformation,[],[f25])).
% 2.03/0.64  fof(f25,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(flattening,[],[f24])).
% 2.03/0.64  fof(f24,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f5])).
% 2.03/0.64  fof(f5,axiom,(
% 2.03/0.64    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).
% 2.03/0.64  fof(f2182,plain,(
% 2.03/0.64    ~r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK1),sK1) | spl8_328),
% 2.03/0.64    inference(avatar_component_clause,[],[f2181])).
% 2.03/0.64  fof(f2195,plain,(
% 2.03/0.64    sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) != k11_lattice3(sK0,sK1,sK1) | v4_waybel_7(sK1,sK0) | ~v4_waybel_7(k11_lattice3(sK0,sK1,sK1),sK0)),
% 2.03/0.64    introduced(theory_tautology_sat_conflict,[])).
% 2.03/0.64  fof(f2183,plain,(
% 2.03/0.64    ~spl8_328 | ~spl8_3 | spl8_177 | ~spl8_284),
% 2.03/0.64    inference(avatar_split_clause,[],[f2175,f1858,f1158,f138,f2181])).
% 2.03/0.64  fof(f1858,plain,(
% 2.03/0.64    spl8_284 <=> ! [X1,X0] : (r1_orders_2(sK0,X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK1) | r1_orders_2(sK0,X1,sK1))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_284])])).
% 2.03/0.64  fof(f2175,plain,(
% 2.03/0.64    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK1),sK1) | (spl8_177 | ~spl8_284)),
% 2.03/0.64    inference(resolution,[],[f2160,f1159])).
% 2.03/0.64  fof(f1159,plain,(
% 2.03/0.64    ~r1_orders_2(sK0,sK1,sK1) | spl8_177),
% 2.03/0.64    inference(avatar_component_clause,[],[f1158])).
% 2.03/0.64  fof(f2160,plain,(
% 2.03/0.64    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,k11_lattice3(sK0,X0,X0),sK1)) ) | ~spl8_284),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f2159])).
% 2.03/0.64  fof(f2159,plain,(
% 2.03/0.64    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,k11_lattice3(sK0,X0,X0),sK1)) ) | ~spl8_284),
% 2.03/0.64    inference(factoring,[],[f1859])).
% 2.03/0.64  fof(f1859,plain,(
% 2.03/0.64    ( ! [X0,X1] : (r1_orders_2(sK0,X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK1) | r1_orders_2(sK0,X1,sK1)) ) | ~spl8_284),
% 2.03/0.64    inference(avatar_component_clause,[],[f1858])).
% 2.03/0.64  fof(f1860,plain,(
% 2.03/0.64    ~spl8_3 | spl8_284 | ~spl8_2 | ~spl8_264),
% 2.03/0.64    inference(avatar_split_clause,[],[f1845,f1666,f134,f1858,f138])).
% 2.03/0.64  fof(f134,plain,(
% 2.03/0.64    spl8_2 <=> v5_waybel_6(sK1,sK0)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.03/0.64  fof(f1666,plain,(
% 2.03/0.64    spl8_264 <=> ! [X1,X0,X2] : (~r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),X2) | r1_orders_2(sK0,X0,X2) | r1_orders_2(sK0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v5_waybel_6(X2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_264])])).
% 2.03/0.64  fof(f1845,plain,(
% 2.03/0.64    ( ! [X0,X1] : (r1_orders_2(sK0,X0,sK1) | r1_orders_2(sK0,X1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_264)),
% 2.03/0.64    inference(resolution,[],[f1667,f135])).
% 2.03/0.64  fof(f135,plain,(
% 2.03/0.64    v5_waybel_6(sK1,sK0) | ~spl8_2),
% 2.03/0.64    inference(avatar_component_clause,[],[f134])).
% 2.03/0.64  fof(f1667,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~v5_waybel_6(X2,sK0) | r1_orders_2(sK0,X0,X2) | r1_orders_2(sK0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl8_264),
% 2.03/0.64    inference(avatar_component_clause,[],[f1666])).
% 2.03/0.64  fof(f1700,plain,(
% 2.03/0.64    ~spl8_237 | ~spl8_80 | ~spl8_3 | spl8_220 | ~spl8_166 | spl8_226),
% 2.03/0.64    inference(avatar_split_clause,[],[f1502,f1457,f1081,f1421,f138,f601,f1504])).
% 2.03/0.64  fof(f1504,plain,(
% 2.03/0.64    spl8_237 <=> r1_orders_2(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),sK1)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_237])])).
% 2.03/0.64  fof(f601,plain,(
% 2.03/0.64    spl8_80 <=> m1_subset_1(k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).
% 2.03/0.64  fof(f1421,plain,(
% 2.03/0.64    spl8_220 <=> k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) = k11_lattice3(sK0,sK1,sK1)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_220])])).
% 2.03/0.64  fof(f1081,plain,(
% 2.03/0.64    spl8_166 <=> ! [X1,X0,X2] : (m1_subset_1(sK3(sK0,X0,X1,X2),u1_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = X2 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X0) | ~r1_orders_2(sK0,X2,X1))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_166])])).
% 2.03/0.64  fof(f1457,plain,(
% 2.03/0.64    spl8_226 <=> m1_subset_1(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),u1_struct_0(sK0))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_226])])).
% 2.03/0.64  fof(f1502,plain,(
% 2.03/0.64    k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) = k11_lattice3(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),sK1) | (~spl8_166 | spl8_226)),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f1500])).
% 2.03/0.64  fof(f1500,plain,(
% 2.03/0.64    k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) = k11_lattice3(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),sK1) | ~r1_orders_2(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),sK1) | (~spl8_166 | spl8_226)),
% 2.03/0.64    inference(resolution,[],[f1458,f1082])).
% 2.03/0.64  fof(f1082,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (m1_subset_1(sK3(sK0,X0,X1,X2),u1_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = X2 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X0) | ~r1_orders_2(sK0,X2,X1)) ) | ~spl8_166),
% 2.03/0.64    inference(avatar_component_clause,[],[f1081])).
% 2.03/0.64  fof(f1458,plain,(
% 2.03/0.64    ~m1_subset_1(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),u1_struct_0(sK0)) | spl8_226),
% 2.03/0.64    inference(avatar_component_clause,[],[f1457])).
% 2.03/0.64  fof(f1695,plain,(
% 2.03/0.64    spl8_39 | ~spl8_7 | ~spl8_5 | ~spl8_4 | ~spl8_3 | ~spl8_80 | ~spl8_237 | spl8_220 | spl8_263),
% 2.03/0.64    inference(avatar_split_clause,[],[f1676,f1661,f1421,f1504,f601,f138,f142,f146,f154,f350])).
% 2.03/0.64  fof(f1661,plain,(
% 2.03/0.64    spl8_263 <=> r1_orders_2(sK0,sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),sK1)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_263])])).
% 2.03/0.64  fof(f1676,plain,(
% 2.03/0.64    k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) = k11_lattice3(sK0,sK1,sK1) | ~r1_orders_2(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),sK1) | ~m1_subset_1(k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | spl8_263),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f1675])).
% 2.03/0.64  fof(f1675,plain,(
% 2.03/0.64    k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) = k11_lattice3(sK0,sK1,sK1) | ~r1_orders_2(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),sK1) | ~r1_orders_2(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),sK1) | ~m1_subset_1(k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | spl8_263),
% 2.03/0.64    inference(resolution,[],[f1662,f90])).
% 2.03/0.64  fof(f90,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) | k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f58])).
% 2.03/0.64  fof(f1662,plain,(
% 2.03/0.64    ~r1_orders_2(sK0,sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),sK1) | spl8_263),
% 2.03/0.64    inference(avatar_component_clause,[],[f1661])).
% 2.03/0.64  fof(f1668,plain,(
% 2.03/0.64    ~spl8_4 | spl8_264 | ~spl8_5),
% 2.03/0.64    inference(avatar_split_clause,[],[f1664,f146,f1666,f142])).
% 2.03/0.64  fof(f1664,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_waybel_6(X2,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,X1,X2) | r1_orders_2(sK0,X0,X2)) ) | ~spl8_5),
% 2.03/0.64    inference(resolution,[],[f726,f147])).
% 2.03/0.64  fof(f147,plain,(
% 2.03/0.64    v2_lattice3(sK0) | ~spl8_5),
% 2.03/0.64    inference(avatar_component_clause,[],[f146])).
% 2.03/0.64  fof(f726,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (~v2_lattice3(X0) | ~r1_orders_2(X0,k11_lattice3(X0,X1,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X2,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X3,X2) | r1_orders_2(X0,X1,X2)) )),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f725])).
% 2.03/0.64  fof(f725,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,k11_lattice3(X0,X1,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X2,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X3,X2) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.03/0.64    inference(resolution,[],[f92,f80])).
% 2.03/0.64  fof(f80,plain,(
% 2.03/0.64    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f21])).
% 2.03/0.64  fof(f21,plain,(
% 2.03/0.64    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 2.03/0.64    inference(flattening,[],[f20])).
% 2.03/0.64  fof(f20,plain,(
% 2.03/0.64    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.03/0.64    inference(ennf_transformation,[],[f2])).
% 2.03/0.64  fof(f2,axiom,(
% 2.03/0.64    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).
% 2.03/0.64  fof(f92,plain,(
% 2.03/0.64    ( ! [X4,X0,X5,X1] : (v2_struct_0(X0) | r1_orders_2(X0,X4,X1) | ~r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X5,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f63])).
% 2.03/0.64  fof(f63,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (((v5_waybel_6(X1,X0) | ((~r1_orders_2(X0,sK5(X0,X1),X1) & ~r1_orders_2(X0,sK4(X0,X1),X1) & r1_orders_2(X0,k11_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r1_orders_2(X0,X5,X1) | r1_orders_2(X0,X4,X1) | ~r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v5_waybel_6(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f60,f62,f61])).
% 2.03/0.64  fof(f61,plain,(
% 2.03/0.64    ! [X1,X0] : (? [X2] : (? [X3] : (~r1_orders_2(X0,X3,X1) & ~r1_orders_2(X0,X2,X1) & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r1_orders_2(X0,X3,X1) & ~r1_orders_2(X0,sK4(X0,X1),X1) & r1_orders_2(X0,k11_lattice3(X0,sK4(X0,X1),X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f62,plain,(
% 2.03/0.64    ! [X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X1) & ~r1_orders_2(X0,sK4(X0,X1),X1) & r1_orders_2(X0,k11_lattice3(X0,sK4(X0,X1),X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1),X1) & ~r1_orders_2(X0,sK4(X0,X1),X1) & r1_orders_2(X0,k11_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f60,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (((v5_waybel_6(X1,X0) | ? [X2] : (? [X3] : (~r1_orders_2(X0,X3,X1) & ~r1_orders_2(X0,X2,X1) & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r1_orders_2(X0,X5,X1) | r1_orders_2(X0,X4,X1) | ~r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v5_waybel_6(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(rectify,[],[f59])).
% 2.03/0.64  fof(f59,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (((v5_waybel_6(X1,X0) | ? [X2] : (? [X3] : (~r1_orders_2(X0,X3,X1) & ~r1_orders_2(X0,X2,X1) & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r1_orders_2(X0,X3,X1) | r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v5_waybel_6(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(nnf_transformation,[],[f27])).
% 2.03/0.64  fof(f27,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : ((v5_waybel_6(X1,X0) <=> ! [X2] : (! [X3] : (r1_orders_2(X0,X3,X1) | r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(flattening,[],[f26])).
% 2.03/0.64  fof(f26,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : ((v5_waybel_6(X1,X0) <=> ! [X2] : (! [X3] : ((r1_orders_2(X0,X3,X1) | r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f12])).
% 2.03/0.64  fof(f12,axiom,(
% 2.03/0.64    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(~r1_orders_2(X0,X3,X1) & ~r1_orders_2(X0,X2,X1) & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)))))))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_6)).
% 2.03/0.64  fof(f1663,plain,(
% 2.03/0.64    spl8_39 | ~spl8_4 | ~spl8_3 | ~spl8_226 | ~spl8_263 | spl8_229),
% 2.03/0.64    inference(avatar_split_clause,[],[f1659,f1468,f1661,f1457,f138,f142,f350])).
% 2.03/0.64  fof(f1468,plain,(
% 2.03/0.64    spl8_229 <=> r2_hidden(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k5_waybel_0(sK0,sK1))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_229])])).
% 2.03/0.64  fof(f1659,plain,(
% 2.03/0.64    ~r1_orders_2(sK0,sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),sK1) | ~m1_subset_1(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | spl8_229),
% 2.03/0.64    inference(resolution,[],[f1469,f99])).
% 2.03/0.64  fof(f99,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f64])).
% 2.03/0.64  fof(f64,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_hidden(X2,k5_waybel_0(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(nnf_transformation,[],[f29])).
% 2.03/0.64  fof(f29,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(flattening,[],[f28])).
% 2.03/0.64  fof(f28,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f11])).
% 2.03/0.64  fof(f11,axiom,(
% 2.03/0.64    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)))))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_0)).
% 2.03/0.64  fof(f1469,plain,(
% 2.03/0.64    ~r2_hidden(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k5_waybel_0(sK0,sK1)) | spl8_229),
% 2.03/0.64    inference(avatar_component_clause,[],[f1468])).
% 2.03/0.64  fof(f1632,plain,(
% 2.03/0.64    ~spl8_3 | ~spl8_2 | spl8_256 | ~spl8_92 | ~spl8_220),
% 2.03/0.64    inference(avatar_split_clause,[],[f1570,f1421,f672,f1630,f134,f138])).
% 2.03/0.64  fof(f1630,plain,(
% 2.03/0.64    spl8_256 <=> v4_waybel_7(k11_lattice3(sK0,sK1,sK1),sK0)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_256])])).
% 2.03/0.64  fof(f672,plain,(
% 2.03/0.64    spl8_92 <=> ! [X0] : (~v5_waybel_6(X0,sK0) | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).
% 2.03/0.64  fof(f1570,plain,(
% 2.03/0.64    v4_waybel_7(k11_lattice3(sK0,sK1,sK1),sK0) | ~v5_waybel_6(sK1,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl8_92 | ~spl8_220)),
% 2.03/0.64    inference(superposition,[],[f673,f1422])).
% 2.03/0.64  fof(f1422,plain,(
% 2.03/0.64    k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) = k11_lattice3(sK0,sK1,sK1) | ~spl8_220),
% 2.03/0.64    inference(avatar_component_clause,[],[f1421])).
% 2.03/0.64  fof(f673,plain,(
% 2.03/0.64    ( ! [X0] : (v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) | ~v5_waybel_6(X0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_92),
% 2.03/0.64    inference(avatar_component_clause,[],[f672])).
% 2.03/0.64  fof(f1499,plain,(
% 2.03/0.64    ~spl8_80 | ~spl8_226 | ~spl8_236 | ~spl8_10 | spl8_219),
% 2.03/0.64    inference(avatar_split_clause,[],[f1455,f1418,f177,f1497,f1457,f601])).
% 2.03/0.64  fof(f1497,plain,(
% 2.03/0.64    spl8_236 <=> r2_hidden(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k5_waybel_0(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_236])])).
% 2.03/0.64  fof(f177,plain,(
% 2.03/0.64    spl8_10 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k5_waybel_0(sK0,X1)) | r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 2.03/0.64  fof(f1418,plain,(
% 2.03/0.64    spl8_219 <=> r1_orders_2(sK0,sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_219])])).
% 2.03/0.64  fof(f1455,plain,(
% 2.03/0.64    ~r2_hidden(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k5_waybel_0(sK0,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)))) | ~m1_subset_1(sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),u1_struct_0(sK0)) | ~m1_subset_1(k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) | (~spl8_10 | spl8_219)),
% 2.03/0.64    inference(resolution,[],[f1419,f178])).
% 2.03/0.64  fof(f178,plain,(
% 2.03/0.64    ( ! [X0,X1] : (r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k5_waybel_0(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl8_10),
% 2.03/0.64    inference(avatar_component_clause,[],[f177])).
% 2.03/0.64  fof(f1419,plain,(
% 2.03/0.64    ~r1_orders_2(sK0,sK3(sK0,sK1,sK1,k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))),k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))) | spl8_219),
% 2.03/0.64    inference(avatar_component_clause,[],[f1418])).
% 2.03/0.64  fof(f1272,plain,(
% 2.03/0.64    spl8_39 | ~spl8_5 | ~spl8_4 | spl8_193 | ~spl8_7),
% 2.03/0.64    inference(avatar_split_clause,[],[f1268,f154,f1270,f142,f146,f350])).
% 2.03/0.64  fof(f1268,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,sK3(sK0,X0,X1,X2),X2) | ~r1_orders_2(sK0,X2,X1) | ~r1_orders_2(sK0,X2,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | k11_lattice3(sK0,X0,X1) = X2 | v2_struct_0(sK0)) ) | ~spl8_7),
% 2.03/0.64    inference(resolution,[],[f91,f155])).
% 2.03/0.64  fof(f155,plain,(
% 2.03/0.64    v5_orders_2(sK0) | ~spl8_7),
% 2.03/0.64    inference(avatar_component_clause,[],[f154])).
% 2.03/0.64  fof(f91,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | k11_lattice3(X0,X1,X2) = X3 | v2_struct_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f58])).
% 2.03/0.64  fof(f1160,plain,(
% 2.03/0.64    spl8_39 | ~spl8_4 | ~spl8_3 | ~spl8_177 | spl8_61),
% 2.03/0.64    inference(avatar_split_clause,[],[f1156,f468,f1158,f138,f142,f350])).
% 2.03/0.64  fof(f468,plain,(
% 2.03/0.64    spl8_61 <=> r2_hidden(sK1,k5_waybel_0(sK0,sK1))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).
% 2.03/0.64  fof(f1156,plain,(
% 2.03/0.64    ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | spl8_61),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f1155])).
% 2.03/0.64  fof(f1155,plain,(
% 2.03/0.64    ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | spl8_61),
% 2.03/0.64    inference(resolution,[],[f469,f99])).
% 2.03/0.64  fof(f469,plain,(
% 2.03/0.64    ~r2_hidden(sK1,k5_waybel_0(sK0,sK1)) | spl8_61),
% 2.03/0.64    inference(avatar_component_clause,[],[f468])).
% 2.03/0.64  fof(f1150,plain,(
% 2.03/0.64    ~spl8_56 | ~spl8_61 | ~spl8_3 | spl8_55 | ~spl8_59 | ~spl8_38 | spl8_54),
% 2.03/0.64    inference(avatar_split_clause,[],[f1149,f432,f337,f460,f435,f138,f468,f438])).
% 2.03/0.64  fof(f460,plain,(
% 2.03/0.64    spl8_59 <=> m1_subset_1(sK7(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).
% 2.03/0.64  fof(f337,plain,(
% 2.03/0.64    spl8_38 <=> ! [X1,X0,X2] : (k1_yellow_0(sK0,X0) = X1 | ~m1_subset_1(sK7(sK0,X1,X0),u1_struct_0(sK0)) | r1_orders_2(sK0,X2,sK7(sK0,X1,X0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X0) | ~r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 2.03/0.64  fof(f1149,plain,(
% 2.03/0.64    ~m1_subset_1(sK7(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) | sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,k5_waybel_0(sK0,sK1)) | ~r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1) | (~spl8_38 | spl8_54)),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f1146])).
% 2.03/0.64  fof(f1146,plain,(
% 2.03/0.64    ~m1_subset_1(sK7(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) | sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,k5_waybel_0(sK0,sK1)) | ~r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl8_38 | spl8_54)),
% 2.03/0.64    inference(resolution,[],[f338,f433])).
% 2.03/0.64  fof(f433,plain,(
% 2.03/0.64    ~r1_orders_2(sK0,sK1,sK7(sK0,sK1,k5_waybel_0(sK0,sK1))) | spl8_54),
% 2.03/0.64    inference(avatar_component_clause,[],[f432])).
% 2.03/0.64  fof(f338,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (r1_orders_2(sK0,X2,sK7(sK0,X1,X0)) | ~m1_subset_1(sK7(sK0,X1,X0),u1_struct_0(sK0)) | k1_yellow_0(sK0,X0) = X1 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X0) | ~r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl8_38),
% 2.03/0.64    inference(avatar_component_clause,[],[f337])).
% 2.03/0.64  fof(f1083,plain,(
% 2.03/0.64    spl8_39 | ~spl8_5 | ~spl8_4 | spl8_166 | ~spl8_7),
% 2.03/0.64    inference(avatar_split_clause,[],[f1079,f154,f1081,f142,f146,f350])).
% 2.03/0.64  fof(f1079,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (m1_subset_1(sK3(sK0,X0,X1,X2),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X1) | ~r1_orders_2(sK0,X2,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | k11_lattice3(sK0,X0,X1) = X2 | v2_struct_0(sK0)) ) | ~spl8_7),
% 2.03/0.64    inference(resolution,[],[f88,f155])).
% 2.03/0.64  fof(f88,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | k11_lattice3(X0,X1,X2) = X3 | v2_struct_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f58])).
% 2.03/0.64  fof(f674,plain,(
% 2.03/0.64    spl8_39 | ~spl8_8 | ~spl8_4 | spl8_92 | ~spl8_91),
% 2.03/0.64    inference(avatar_split_clause,[],[f670,f666,f672,f142,f158,f350])).
% 2.03/0.64  fof(f158,plain,(
% 2.03/0.64    spl8_8 <=> v4_orders_2(sK0)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 2.03/0.64  fof(f666,plain,(
% 2.03/0.64    spl8_91 <=> ! [X0] : (v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) | ~v5_waybel_6(X0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v12_waybel_0(k5_waybel_0(sK0,X0),sK0))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).
% 2.03/0.64  fof(f670,plain,(
% 2.03/0.64    ( ! [X0] : (~v5_waybel_6(X0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) | ~l1_orders_2(sK0) | ~v4_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl8_91),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f669])).
% 2.03/0.64  fof(f669,plain,(
% 2.03/0.64    ( ! [X0] : (~v5_waybel_6(X0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v4_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl8_91),
% 2.03/0.64    inference(resolution,[],[f667,f117])).
% 2.03/0.64  fof(f117,plain,(
% 2.03/0.64    ( ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f38])).
% 2.03/0.64  fof(f38,plain,(
% 2.03/0.64    ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(flattening,[],[f37])).
% 2.03/0.64  fof(f37,plain,(
% 2.03/0.64    ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f9])).
% 2.03/0.64  fof(f9,axiom,(
% 2.03/0.64    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => v12_waybel_0(k5_waybel_0(X0,X1),X0))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_waybel_0)).
% 2.03/0.64  fof(f667,plain,(
% 2.03/0.64    ( ! [X0] : (~v12_waybel_0(k5_waybel_0(sK0,X0),sK0) | ~v5_waybel_6(X0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)) ) | ~spl8_91),
% 2.03/0.64    inference(avatar_component_clause,[],[f666])).
% 2.03/0.64  fof(f668,plain,(
% 2.03/0.64    spl8_39 | ~spl8_9 | ~spl8_4 | spl8_91 | ~spl8_90),
% 2.03/0.64    inference(avatar_split_clause,[],[f664,f660,f666,f142,f162,f350])).
% 2.03/0.64  fof(f162,plain,(
% 2.03/0.64    spl8_9 <=> v3_orders_2(sK0)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 2.03/0.64  fof(f660,plain,(
% 2.03/0.64    spl8_90 <=> ! [X0] : (~v5_waybel_6(X0,sK0) | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) | ~v12_waybel_0(k5_waybel_0(sK0,X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(k5_waybel_0(sK0,X0)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_90])])).
% 2.03/0.64  fof(f664,plain,(
% 2.03/0.64    ( ! [X0] : (v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) | ~v12_waybel_0(k5_waybel_0(sK0,X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_waybel_6(X0,sK0) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl8_90),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f663])).
% 2.03/0.64  fof(f663,plain,(
% 2.03/0.64    ( ! [X0] : (v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) | ~v12_waybel_0(k5_waybel_0(sK0,X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_waybel_6(X0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl8_90),
% 2.03/0.64    inference(resolution,[],[f661,f118])).
% 2.03/0.64  fof(f118,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~v1_xboole_0(k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f40])).
% 2.03/0.64  fof(f40,plain,(
% 2.03/0.64    ! [X0,X1] : ((v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(flattening,[],[f39])).
% 2.03/0.64  fof(f39,plain,(
% 2.03/0.64    ! [X0,X1] : ((v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f10])).
% 2.03/0.64  fof(f10,axiom,(
% 2.03/0.64    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_waybel_0)).
% 2.03/0.64  fof(f661,plain,(
% 2.03/0.64    ( ! [X0] : (v1_xboole_0(k5_waybel_0(sK0,X0)) | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) | ~v12_waybel_0(k5_waybel_0(sK0,X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_waybel_6(X0,sK0)) ) | ~spl8_90),
% 2.03/0.64    inference(avatar_component_clause,[],[f660])).
% 2.03/0.64  fof(f662,plain,(
% 2.03/0.64    spl8_39 | ~spl8_9 | ~spl8_4 | spl8_90 | ~spl8_89),
% 2.03/0.64    inference(avatar_split_clause,[],[f658,f654,f660,f142,f162,f350])).
% 2.03/0.64  fof(f654,plain,(
% 2.03/0.64    spl8_89 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_waybel_6(X0,sK0) | v1_xboole_0(k5_waybel_0(sK0,X0)) | ~v1_waybel_0(k5_waybel_0(sK0,X0),sK0) | ~v12_waybel_0(k5_waybel_0(sK0,X0),sK0) | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).
% 2.03/0.64  fof(f658,plain,(
% 2.03/0.64    ( ! [X0] : (~v5_waybel_6(X0,sK0) | v1_xboole_0(k5_waybel_0(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v12_waybel_0(k5_waybel_0(sK0,X0),sK0) | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl8_89),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f657])).
% 2.03/0.64  fof(f657,plain,(
% 2.03/0.64    ( ! [X0] : (~v5_waybel_6(X0,sK0) | v1_xboole_0(k5_waybel_0(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v12_waybel_0(k5_waybel_0(sK0,X0),sK0) | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl8_89),
% 2.03/0.64    inference(resolution,[],[f655,f119])).
% 2.03/0.64  fof(f119,plain,(
% 2.03/0.64    ( ! [X0,X1] : (v1_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f40])).
% 2.03/0.64  fof(f655,plain,(
% 2.03/0.64    ( ! [X0] : (~v1_waybel_0(k5_waybel_0(sK0,X0),sK0) | ~v5_waybel_6(X0,sK0) | v1_xboole_0(k5_waybel_0(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v12_waybel_0(k5_waybel_0(sK0,X0),sK0) | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0)) ) | ~spl8_89),
% 2.03/0.64    inference(avatar_component_clause,[],[f654])).
% 2.03/0.64  fof(f656,plain,(
% 2.03/0.64    ~spl8_9 | ~spl8_8 | ~spl8_7 | ~spl8_6 | ~spl8_5 | ~spl8_4 | spl8_89 | ~spl8_88),
% 2.03/0.64    inference(avatar_split_clause,[],[f651,f647,f654,f142,f146,f150,f154,f158,f162])).
% 2.03/0.64  fof(f150,plain,(
% 2.03/0.64    spl8_6 <=> v1_lattice3(sK0)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 2.03/0.64  fof(f647,plain,(
% 2.03/0.64    spl8_88 <=> ! [X0] : (v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_waybel_7(k5_waybel_0(sK0,X0),sK0) | ~v12_waybel_0(k5_waybel_0(sK0,X0),sK0) | ~v1_waybel_0(k5_waybel_0(sK0,X0),sK0) | v1_xboole_0(k5_waybel_0(sK0,X0)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).
% 2.03/0.64  fof(f651,plain,(
% 2.03/0.64    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) | ~v12_waybel_0(k5_waybel_0(sK0,X0),sK0) | ~v1_waybel_0(k5_waybel_0(sK0,X0),sK0) | v1_xboole_0(k5_waybel_0(sK0,X0)) | ~v5_waybel_6(X0,sK0) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)) ) | ~spl8_88),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f650])).
% 2.03/0.64  fof(f650,plain,(
% 2.03/0.64    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) | ~v12_waybel_0(k5_waybel_0(sK0,X0),sK0) | ~v1_waybel_0(k5_waybel_0(sK0,X0),sK0) | v1_xboole_0(k5_waybel_0(sK0,X0)) | ~v5_waybel_6(X0,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)) ) | ~spl8_88),
% 2.03/0.64    inference(resolution,[],[f648,f100])).
% 2.03/0.64  fof(f100,plain,(
% 2.03/0.64    ( ! [X0,X1] : (v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f31])).
% 2.03/0.64  fof(f31,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 2.03/0.64    inference(flattening,[],[f30])).
% 2.03/0.64  fof(f30,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : ((v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f14])).
% 2.03/0.64  fof(f14,axiom,(
% 2.03/0.64    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v1_waybel_7(k5_waybel_0(X0,X1),X0))))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_7)).
% 2.03/0.64  fof(f648,plain,(
% 2.03/0.64    ( ! [X0] : (~v1_waybel_7(k5_waybel_0(sK0,X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) | ~v12_waybel_0(k5_waybel_0(sK0,X0),sK0) | ~v1_waybel_0(k5_waybel_0(sK0,X0),sK0) | v1_xboole_0(k5_waybel_0(sK0,X0))) ) | ~spl8_88),
% 2.03/0.64    inference(avatar_component_clause,[],[f647])).
% 2.03/0.64  fof(f649,plain,(
% 2.03/0.64    spl8_39 | ~spl8_4 | spl8_88 | ~spl8_87),
% 2.03/0.64    inference(avatar_split_clause,[],[f645,f642,f647,f142,f350])).
% 2.03/0.64  fof(f642,plain,(
% 2.03/0.64    spl8_87 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_waybel_7(k1_yellow_0(sK0,X0),sK0) | v1_xboole_0(X0) | ~v1_waybel_0(X0,sK0) | ~v12_waybel_0(X0,sK0) | ~v1_waybel_7(X0,sK0))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).
% 2.03/0.64  fof(f645,plain,(
% 2.03/0.64    ( ! [X0] : (v4_waybel_7(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK0) | v1_xboole_0(k5_waybel_0(sK0,X0)) | ~v1_waybel_0(k5_waybel_0(sK0,X0),sK0) | ~v12_waybel_0(k5_waybel_0(sK0,X0),sK0) | ~v1_waybel_7(k5_waybel_0(sK0,X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl8_87),
% 2.03/0.64    inference(resolution,[],[f643,f120])).
% 2.03/0.64  fof(f120,plain,(
% 2.03/0.64    ( ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f42])).
% 2.03/0.64  fof(f42,plain,(
% 2.03/0.64    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.03/0.64    inference(flattening,[],[f41])).
% 2.03/0.64  fof(f41,plain,(
% 2.03/0.64    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f8])).
% 2.03/0.64  fof(f8,axiom,(
% 2.03/0.64    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).
% 2.03/0.64  fof(f643,plain,(
% 2.03/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_waybel_7(k1_yellow_0(sK0,X0),sK0) | v1_xboole_0(X0) | ~v1_waybel_0(X0,sK0) | ~v12_waybel_0(X0,sK0) | ~v1_waybel_7(X0,sK0)) ) | ~spl8_87),
% 2.03/0.64    inference(avatar_component_clause,[],[f642])).
% 2.03/0.64  fof(f644,plain,(
% 2.03/0.64    ~spl8_9 | ~spl8_8 | ~spl8_7 | ~spl8_5 | ~spl8_4 | spl8_87 | ~spl8_6),
% 2.03/0.64    inference(avatar_split_clause,[],[f638,f150,f642,f142,f146,f154,f158,f162])).
% 2.03/0.64  fof(f638,plain,(
% 2.03/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_waybel_7(X0,sK0) | ~v12_waybel_0(X0,sK0) | ~v1_waybel_0(X0,sK0) | v1_xboole_0(X0) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | v4_waybel_7(k1_yellow_0(sK0,X0),sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)) ) | ~spl8_6),
% 2.03/0.64    inference(resolution,[],[f167,f151])).
% 2.03/0.64  fof(f151,plain,(
% 2.03/0.64    v1_lattice3(sK0) | ~spl8_6),
% 2.03/0.64    inference(avatar_component_clause,[],[f150])).
% 2.03/0.64  fof(f167,plain,(
% 2.03/0.64    ( ! [X2,X0] : (~v1_lattice3(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | v4_waybel_7(k1_yellow_0(X0,X2),X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 2.03/0.64    inference(subsumption_resolution,[],[f126,f116])).
% 2.03/0.64  fof(f116,plain,(
% 2.03/0.64    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f36])).
% 2.03/0.64  fof(f36,plain,(
% 2.03/0.64    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.03/0.64    inference(ennf_transformation,[],[f6])).
% 2.03/0.64  fof(f6,axiom,(
% 2.03/0.64    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 2.03/0.64  fof(f126,plain,(
% 2.03/0.64    ( ! [X2,X0] : (v4_waybel_7(k1_yellow_0(X0,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | ~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 2.03/0.64    inference(equality_resolution,[],[f107])).
% 2.03/0.64  fof(f107,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (v4_waybel_7(X1,X0) | k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f68])).
% 2.03/0.64  fof(f68,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & ((k1_yellow_0(X0,sK6(X0,X1)) = X1 & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(sK6(X0,X1),X0) & v12_waybel_0(sK6(X0,X1),X0) & v1_waybel_0(sK6(X0,X1),X0) & ~v1_xboole_0(sK6(X0,X1))) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f66,f67])).
% 2.03/0.64  fof(f67,plain,(
% 2.03/0.64    ! [X1,X0] : (? [X3] : (k1_yellow_0(X0,X3) = X1 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X3,X0) & v12_waybel_0(X3,X0) & v1_waybel_0(X3,X0) & ~v1_xboole_0(X3)) => (k1_yellow_0(X0,sK6(X0,X1)) = X1 & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(sK6(X0,X1),X0) & v12_waybel_0(sK6(X0,X1),X0) & v1_waybel_0(sK6(X0,X1),X0) & ~v1_xboole_0(sK6(X0,X1))))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f66,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & (? [X3] : (k1_yellow_0(X0,X3) = X1 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X3,X0) & v12_waybel_0(X3,X0) & v1_waybel_0(X3,X0) & ~v1_xboole_0(X3)) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 2.03/0.64    inference(rectify,[],[f65])).
% 2.03/0.64  fof(f65,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & (? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2)) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 2.03/0.64    inference(nnf_transformation,[],[f33])).
% 2.03/0.64  fof(f33,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 2.03/0.64    inference(flattening,[],[f32])).
% 2.03/0.64  fof(f32,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f13])).
% 2.03/0.64  fof(f13,axiom,(
% 2.03/0.64    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2)))))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_7)).
% 2.03/0.64  fof(f609,plain,(
% 2.03/0.64    ~spl8_4 | spl8_80),
% 2.03/0.64    inference(avatar_split_clause,[],[f607,f601,f142])).
% 2.03/0.64  fof(f607,plain,(
% 2.03/0.64    ~l1_orders_2(sK0) | spl8_80),
% 2.03/0.64    inference(resolution,[],[f602,f116])).
% 2.03/0.64  fof(f602,plain,(
% 2.03/0.64    ~m1_subset_1(k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) | spl8_80),
% 2.03/0.64    inference(avatar_component_clause,[],[f601])).
% 2.03/0.64  fof(f567,plain,(
% 2.03/0.64    ~spl8_4 | ~spl8_3 | spl8_56 | spl8_72),
% 2.03/0.64    inference(avatar_split_clause,[],[f565,f520,f438,f138,f142])).
% 2.03/0.64  fof(f520,plain,(
% 2.03/0.64    spl8_72 <=> r2_hidden(sK2(sK0,k5_waybel_0(sK0,sK1),sK1),k5_waybel_0(sK0,sK1))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).
% 2.03/0.64  fof(f565,plain,(
% 2.03/0.64    r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | spl8_72),
% 2.03/0.64    inference(resolution,[],[f521,f83])).
% 2.03/0.64  fof(f83,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f53])).
% 2.03/0.64  fof(f53,plain,(
% 2.03/0.64    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).
% 2.03/0.64  fof(f52,plain,(
% 2.03/0.64    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f51,plain,(
% 2.03/0.64    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.03/0.64    inference(rectify,[],[f50])).
% 2.03/0.64  fof(f50,plain,(
% 2.03/0.64    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.03/0.64    inference(nnf_transformation,[],[f23])).
% 2.03/0.64  fof(f23,plain,(
% 2.03/0.64    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.03/0.64    inference(flattening,[],[f22])).
% 2.03/0.64  fof(f22,plain,(
% 2.03/0.64    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.03/0.64    inference(ennf_transformation,[],[f3])).
% 2.03/0.64  fof(f3,axiom,(
% 2.03/0.64    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 2.03/0.64  fof(f521,plain,(
% 2.03/0.64    ~r2_hidden(sK2(sK0,k5_waybel_0(sK0,sK1),sK1),k5_waybel_0(sK0,sK1)) | spl8_72),
% 2.03/0.64    inference(avatar_component_clause,[],[f520])).
% 2.03/0.64  fof(f525,plain,(
% 2.03/0.64    ~spl8_4 | ~spl8_3 | spl8_56 | spl8_68),
% 2.03/0.64    inference(avatar_split_clause,[],[f523,f505,f438,f138,f142])).
% 2.03/0.64  fof(f505,plain,(
% 2.03/0.64    spl8_68 <=> m1_subset_1(sK2(sK0,k5_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).
% 2.03/0.64  fof(f523,plain,(
% 2.03/0.64    r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | spl8_68),
% 2.03/0.64    inference(resolution,[],[f506,f82])).
% 2.03/0.64  fof(f82,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f53])).
% 2.03/0.64  fof(f506,plain,(
% 2.03/0.64    ~m1_subset_1(sK2(sK0,k5_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0)) | spl8_68),
% 2.03/0.64    inference(avatar_component_clause,[],[f505])).
% 2.03/0.64  fof(f522,plain,(
% 2.03/0.64    ~spl8_68 | ~spl8_3 | ~spl8_72 | ~spl8_11 | spl8_56),
% 2.03/0.64    inference(avatar_split_clause,[],[f503,f438,f183,f520,f138,f505])).
% 2.03/0.64  fof(f183,plain,(
% 2.03/0.64    spl8_11 <=> ! [X1,X0] : (~r2_hidden(sK2(sK0,X0,X1),k5_waybel_0(sK0,X1)) | r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 2.03/0.64  fof(f503,plain,(
% 2.03/0.64    ~r2_hidden(sK2(sK0,k5_waybel_0(sK0,sK1),sK1),k5_waybel_0(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2(sK0,k5_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0)) | (~spl8_11 | spl8_56)),
% 2.03/0.64    inference(resolution,[],[f452,f184])).
% 2.03/0.64  fof(f184,plain,(
% 2.03/0.64    ( ! [X0,X1] : (r2_lattice3(sK0,X0,X1) | ~r2_hidden(sK2(sK0,X0,X1),k5_waybel_0(sK0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))) ) | ~spl8_11),
% 2.03/0.64    inference(avatar_component_clause,[],[f183])).
% 2.03/0.64  fof(f452,plain,(
% 2.03/0.64    ~r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1) | spl8_56),
% 2.03/0.64    inference(avatar_component_clause,[],[f438])).
% 2.03/0.64  fof(f494,plain,(
% 2.03/0.64    ~spl8_7 | ~spl8_4 | ~spl8_3 | ~spl8_56 | spl8_55 | spl8_59),
% 2.03/0.64    inference(avatar_split_clause,[],[f491,f460,f435,f438,f138,f142,f154])).
% 2.03/0.64  fof(f491,plain,(
% 2.03/0.64    sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | ~r2_lattice3(sK0,k5_waybel_0(sK0,sK1),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | spl8_59),
% 2.03/0.64    inference(resolution,[],[f461,f110])).
% 2.03/0.64  fof(f110,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X2) = X1 | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f70])).
% 2.03/0.64  fof(f70,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK7(X0,X1,X2)) & r2_lattice3(X0,X2,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f69])).
% 2.03/0.64  fof(f69,plain,(
% 2.03/0.64    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK7(X0,X1,X2)) & r2_lattice3(X0,X2,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f35,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.03/0.64    inference(flattening,[],[f34])).
% 2.03/0.64  fof(f34,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f17])).
% 2.03/0.64  fof(f17,plain,(
% 2.03/0.64    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 2.03/0.64    inference(rectify,[],[f7])).
% 2.03/0.64  fof(f7,axiom,(
% 2.03/0.64    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).
% 2.03/0.64  fof(f461,plain,(
% 2.03/0.64    ~m1_subset_1(sK7(sK0,sK1,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) | spl8_59),
% 2.03/0.64    inference(avatar_component_clause,[],[f460])).
% 2.03/0.64  fof(f427,plain,(
% 2.03/0.64    ~spl8_4 | ~spl8_5 | ~spl8_39),
% 2.03/0.64    inference(avatar_split_clause,[],[f425,f350,f146,f142])).
% 2.03/0.64  fof(f425,plain,(
% 2.03/0.64    ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~spl8_39),
% 2.03/0.64    inference(resolution,[],[f351,f80])).
% 2.03/0.64  fof(f351,plain,(
% 2.03/0.64    v2_struct_0(sK0) | ~spl8_39),
% 2.03/0.64    inference(avatar_component_clause,[],[f350])).
% 2.03/0.64  fof(f339,plain,(
% 2.03/0.64    ~spl8_4 | spl8_38 | ~spl8_36),
% 2.03/0.64    inference(avatar_split_clause,[],[f335,f327,f337,f142])).
% 2.03/0.64  fof(f327,plain,(
% 2.03/0.64    spl8_36 <=> ! [X1,X0] : (r2_lattice3(sK0,X0,sK7(sK0,X1,X0)) | k1_yellow_0(sK0,X0) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,X1))),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 2.03/0.64  fof(f335,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (k1_yellow_0(sK0,X0) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,X1) | ~r2_hidden(X2,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_orders_2(sK0,X2,sK7(sK0,X1,X0)) | ~m1_subset_1(sK7(sK0,X1,X0),u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl8_36),
% 2.03/0.64    inference(resolution,[],[f328,f81])).
% 2.03/0.64  fof(f81,plain,(
% 2.03/0.64    ( ! [X4,X2,X0,X1] : (~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f53])).
% 2.03/0.64  fof(f328,plain,(
% 2.03/0.64    ( ! [X0,X1] : (r2_lattice3(sK0,X0,sK7(sK0,X1,X0)) | k1_yellow_0(sK0,X0) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,X1)) ) | ~spl8_36),
% 2.03/0.64    inference(avatar_component_clause,[],[f327])).
% 2.03/0.64  fof(f334,plain,(
% 2.03/0.64    ~spl8_4 | spl8_37 | ~spl8_7),
% 2.03/0.64    inference(avatar_split_clause,[],[f330,f154,f332,f142])).
% 2.03/0.64  fof(f330,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,sK7(sK0,X0,X1)) | ~r2_lattice3(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | k1_yellow_0(sK0,X1) = X0) ) | ~spl8_7),
% 2.03/0.64    inference(resolution,[],[f112,f155])).
% 2.03/0.64  fof(f112,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~r1_orders_2(X0,X1,sK7(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k1_yellow_0(X0,X2) = X1) )),
% 2.03/0.64    inference(cnf_transformation,[],[f70])).
% 2.03/0.64  fof(f329,plain,(
% 2.03/0.64    ~spl8_4 | spl8_36 | ~spl8_7),
% 2.03/0.64    inference(avatar_split_clause,[],[f325,f154,f327,f142])).
% 2.03/0.64  fof(f325,plain,(
% 2.03/0.64    ( ! [X0,X1] : (r2_lattice3(sK0,X0,sK7(sK0,X1,X0)) | ~r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | k1_yellow_0(sK0,X0) = X1) ) | ~spl8_7),
% 2.03/0.64    inference(resolution,[],[f111,f155])).
% 2.03/0.64  fof(f111,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | r2_lattice3(X0,X2,sK7(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k1_yellow_0(X0,X2) = X1) )),
% 2.03/0.64    inference(cnf_transformation,[],[f70])).
% 2.03/0.64  fof(f185,plain,(
% 2.03/0.64    ~spl8_4 | spl8_11 | ~spl8_10),
% 2.03/0.64    inference(avatar_split_clause,[],[f181,f177,f183,f142])).
% 2.03/0.64  fof(f181,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~r2_hidden(sK2(sK0,X0,X1),k5_waybel_0(sK0,X1)) | ~m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1) | ~l1_orders_2(sK0)) ) | ~spl8_10),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f180])).
% 2.03/0.64  fof(f180,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~r2_hidden(sK2(sK0,X0,X1),k5_waybel_0(sK0,X1)) | ~m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl8_10),
% 2.03/0.64    inference(resolution,[],[f178,f84])).
% 2.03/0.64  fof(f84,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK2(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f53])).
% 2.03/0.64  fof(f179,plain,(
% 2.03/0.64    ~spl8_4 | spl8_10 | ~spl8_5),
% 2.03/0.64    inference(avatar_split_clause,[],[f174,f146,f177,f142])).
% 2.03/0.64  fof(f174,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k5_waybel_0(sK0,X1))) ) | ~spl8_5),
% 2.03/0.64    inference(resolution,[],[f173,f147])).
% 2.03/0.64  fof(f173,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~v2_lattice3(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | r1_orders_2(X1,X0,X2) | ~r2_hidden(X0,k5_waybel_0(X1,X2))) )),
% 2.03/0.64    inference(duplicate_literal_removal,[],[f172])).
% 2.03/0.64  fof(f172,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_waybel_0(X1,X2)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | r1_orders_2(X1,X0,X2) | ~v2_lattice3(X1) | ~l1_orders_2(X1)) )),
% 2.03/0.64    inference(resolution,[],[f98,f80])).
% 2.03/0.64  fof(f98,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~r2_hidden(X2,k5_waybel_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X2,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f64])).
% 2.03/0.64  fof(f164,plain,(
% 2.03/0.64    spl8_9),
% 2.03/0.64    inference(avatar_split_clause,[],[f71,f162])).
% 2.03/0.64  fof(f71,plain,(
% 2.03/0.64    v3_orders_2(sK0)),
% 2.03/0.64    inference(cnf_transformation,[],[f49])).
% 2.03/0.64  fof(f49,plain,(
% 2.03/0.64    (~v4_waybel_7(sK1,sK0) & v5_waybel_6(sK1,sK0) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0)),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f48,f47])).
% 2.03/0.64  fof(f47,plain,(
% 2.03/0.64    ? [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (~v4_waybel_7(X1,sK0) & v5_waybel_6(X1,sK0) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f48,plain,(
% 2.03/0.64    ? [X1] : (~v4_waybel_7(X1,sK0) & v5_waybel_6(X1,sK0) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v4_waybel_7(sK1,sK0) & v5_waybel_6(sK1,sK0) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f19,plain,(
% 2.03/0.64    ? [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0))),
% 2.03/0.64    inference(flattening,[],[f18])).
% 2.03/0.64  fof(f18,plain,(
% 2.03/0.64    ? [X0] : (? [X1] : ((~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f16])).
% 2.03/0.64  fof(f16,negated_conjecture,(
% 2.03/0.64    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v4_waybel_7(X1,X0))))),
% 2.03/0.64    inference(negated_conjecture,[],[f15])).
% 2.03/0.64  fof(f15,conjecture,(
% 2.03/0.64    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v4_waybel_7(X1,X0))))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_7)).
% 2.03/0.64  fof(f160,plain,(
% 2.03/0.64    spl8_8),
% 2.03/0.64    inference(avatar_split_clause,[],[f72,f158])).
% 2.03/0.64  fof(f72,plain,(
% 2.03/0.64    v4_orders_2(sK0)),
% 2.03/0.64    inference(cnf_transformation,[],[f49])).
% 2.03/0.64  fof(f156,plain,(
% 2.03/0.64    spl8_7),
% 2.03/0.64    inference(avatar_split_clause,[],[f73,f154])).
% 2.03/0.64  fof(f73,plain,(
% 2.03/0.64    v5_orders_2(sK0)),
% 2.03/0.64    inference(cnf_transformation,[],[f49])).
% 2.03/0.64  fof(f152,plain,(
% 2.03/0.64    spl8_6),
% 2.03/0.64    inference(avatar_split_clause,[],[f74,f150])).
% 2.03/0.64  fof(f74,plain,(
% 2.03/0.64    v1_lattice3(sK0)),
% 2.03/0.64    inference(cnf_transformation,[],[f49])).
% 2.03/0.64  fof(f148,plain,(
% 2.03/0.64    spl8_5),
% 2.03/0.64    inference(avatar_split_clause,[],[f75,f146])).
% 2.03/0.64  fof(f75,plain,(
% 2.03/0.64    v2_lattice3(sK0)),
% 2.03/0.64    inference(cnf_transformation,[],[f49])).
% 2.03/0.64  fof(f144,plain,(
% 2.03/0.64    spl8_4),
% 2.03/0.64    inference(avatar_split_clause,[],[f76,f142])).
% 2.03/0.64  fof(f76,plain,(
% 2.03/0.64    l1_orders_2(sK0)),
% 2.03/0.64    inference(cnf_transformation,[],[f49])).
% 2.03/0.64  fof(f140,plain,(
% 2.03/0.64    spl8_3),
% 2.03/0.64    inference(avatar_split_clause,[],[f77,f138])).
% 2.03/0.64  fof(f77,plain,(
% 2.03/0.64    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.03/0.64    inference(cnf_transformation,[],[f49])).
% 2.03/0.64  fof(f136,plain,(
% 2.03/0.64    spl8_2),
% 2.03/0.64    inference(avatar_split_clause,[],[f78,f134])).
% 2.03/0.64  fof(f78,plain,(
% 2.03/0.64    v5_waybel_6(sK1,sK0)),
% 2.03/0.64    inference(cnf_transformation,[],[f49])).
% 2.03/0.64  fof(f132,plain,(
% 2.03/0.64    ~spl8_1),
% 2.03/0.64    inference(avatar_split_clause,[],[f79,f130])).
% 2.03/0.64  fof(f130,plain,(
% 2.03/0.64    spl8_1 <=> v4_waybel_7(sK1,sK0)),
% 2.03/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.03/0.64  fof(f79,plain,(
% 2.03/0.64    ~v4_waybel_7(sK1,sK0)),
% 2.03/0.64    inference(cnf_transformation,[],[f49])).
% 2.03/0.64  % SZS output end Proof for theBenchmark
% 2.03/0.64  % (8180)------------------------------
% 2.03/0.64  % (8180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.64  % (8180)Termination reason: Refutation
% 2.03/0.64  
% 2.03/0.64  % (8180)Memory used [KB]: 12665
% 2.03/0.64  % (8180)Time elapsed: 0.200 s
% 2.03/0.64  % (8180)------------------------------
% 2.03/0.64  % (8180)------------------------------
% 2.03/0.65  % (8173)Success in time 0.272 s
%------------------------------------------------------------------------------
