%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2049+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:05 EST 2020

% Result     : Theorem 2.88s
% Output     : Refutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  473 (1443 expanded)
%              Number of leaves         :   71 ( 531 expanded)
%              Depth                    :   32
%              Number of atoms          : 3197 (9438 expanded)
%              Number of equality atoms :  244 (1194 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2180,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f168,f173,f178,f183,f188,f193,f198,f203,f208,f213,f218,f223,f228,f234,f257,f276,f344,f377,f395,f404,f458,f502,f560,f570,f730,f756,f764,f859,f881,f960,f1035,f1702,f1728,f1751,f1835,f1895,f1920,f1980,f2012,f2179])).

fof(f2179,plain,
    ( ~ spl11_2
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_22
    | ~ spl11_28
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56
    | spl11_68
    | spl11_69 ),
    inference(avatar_contradiction_clause,[],[f2178])).

fof(f2178,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_22
    | ~ spl11_28
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56
    | spl11_68
    | spl11_69 ),
    inference(subsumption_resolution,[],[f2177,f456])).

fof(f456,plain,
    ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f455])).

fof(f455,plain,
    ( spl11_28
  <=> r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f2177,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_22
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56
    | spl11_68
    | spl11_69 ),
    inference(equality_resolution,[],[f2106])).

fof(f2106,plain,
    ( ! [X0] :
        ( sK3 != X0
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_22
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56
    | spl11_68
    | spl11_69 ),
    inference(subsumption_resolution,[],[f2105,f1247])).

fof(f1247,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0))
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))) )
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(duplicate_literal_removal,[],[f1242])).

fof(f1242,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0))
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))) )
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(superposition,[],[f1164,f1169])).

fof(f1169,plain,
    ( ! [X2] :
        ( sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X2) = sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X2))
        | ~ r2_hidden(X2,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))) )
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1168,f217])).

fof(f217,plain,
    ( ~ v2_struct_0(sK0)
    | spl11_12 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl11_12
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f1168,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X2) = sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X2))
        | v2_struct_0(sK0) )
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_11
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1167,f212])).

fof(f212,plain,
    ( l1_struct_0(sK0)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl11_11
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f1167,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X2) = sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X2))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1166,f207])).

fof(f207,plain,
    ( ~ v2_struct_0(sK1)
    | spl11_10 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl11_10
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f1166,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X2) = sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X2))
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1165,f192])).

fof(f192,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl11_7
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f1165,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X2) = sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X2))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_6
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1153,f187])).

fof(f187,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl11_6
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f1153,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X2) = sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X2))
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(resolution,[],[f1102,f397])).

fof(f397,plain,(
    ! [X2,X0,X7,X1] :
      ( ~ r2_hidden(X7,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | sK7(X1,X2,X7) = X7
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f396,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(f396,plain,(
    ! [X2,X0,X7,X1] :
      ( sK7(X1,X2,X7) = X7
      | ~ r2_hidden(X7,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f150,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f150,plain,(
    ! [X2,X0,X7,X1] :
      ( sK7(X1,X2,X7) = X7
      | ~ r2_hidden(X7,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( sK7(X1,X2,X7) = X7
      | ~ r2_hidden(X7,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ( ( ! [X5] :
                              ( ~ r1_orders_2(X1,X2,X5)
                              | sK5(X1,X2,X3) != X5
                              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                          | ~ r2_hidden(sK5(X1,X2,X3),u1_struct_0(X3)) )
                        & ( ( r1_orders_2(X1,X2,sK6(X1,X2,X3))
                            & sK5(X1,X2,X3) = sK6(X1,X2,X3)
                            & m1_subset_1(sK6(X1,X2,X3),u1_struct_0(X1)) )
                          | r2_hidden(sK5(X1,X2,X3),u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X7] :
                            ( ( r2_hidden(X7,u1_struct_0(X3))
                              | ! [X8] :
                                  ( ~ r1_orders_2(X1,X2,X8)
                                  | X7 != X8
                                  | ~ m1_subset_1(X8,u1_struct_0(X1)) ) )
                            & ( ( r1_orders_2(X1,X2,sK7(X1,X2,X7))
                                & sK7(X1,X2,X7) = X7
                                & m1_subset_1(sK7(X1,X2,X7),u1_struct_0(X1)) )
                              | ~ r2_hidden(X7,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f71,f74,f73,f72])).

fof(f72,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_orders_2(X1,X2,X5)
                | X4 != X5
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r2_hidden(X4,u1_struct_0(X3)) )
          & ( ? [X6] :
                ( r1_orders_2(X1,X2,X6)
                & X4 = X6
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | r2_hidden(X4,u1_struct_0(X3)) ) )
     => ( ( ! [X5] :
              ( ~ r1_orders_2(X1,X2,X5)
              | sK5(X1,X2,X3) != X5
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(sK5(X1,X2,X3),u1_struct_0(X3)) )
        & ( ? [X6] :
              ( r1_orders_2(X1,X2,X6)
              & sK5(X1,X2,X3) = X6
              & m1_subset_1(X6,u1_struct_0(X1)) )
          | r2_hidden(sK5(X1,X2,X3),u1_struct_0(X3)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X3,X2,X1] :
      ( ? [X6] :
          ( r1_orders_2(X1,X2,X6)
          & sK5(X1,X2,X3) = X6
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X2,sK6(X1,X2,X3))
        & sK5(X1,X2,X3) = sK6(X1,X2,X3)
        & m1_subset_1(sK6(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X7,X2,X1] :
      ( ? [X9] :
          ( r1_orders_2(X1,X2,X9)
          & X7 = X9
          & m1_subset_1(X9,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X2,sK7(X1,X2,X7))
        & sK7(X1,X2,X7) = X7
        & m1_subset_1(sK7(X1,X2,X7),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( ~ r1_orders_2(X1,X2,X5)
                                | X4 != X5
                                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                            | ~ r2_hidden(X4,u1_struct_0(X3)) )
                          & ( ? [X6] :
                                ( r1_orders_2(X1,X2,X6)
                                & X4 = X6
                                & m1_subset_1(X6,u1_struct_0(X1)) )
                            | r2_hidden(X4,u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X7] :
                            ( ( r2_hidden(X7,u1_struct_0(X3))
                              | ! [X8] :
                                  ( ~ r1_orders_2(X1,X2,X8)
                                  | X7 != X8
                                  | ~ m1_subset_1(X8,u1_struct_0(X1)) ) )
                            & ( ? [X9] :
                                  ( r1_orders_2(X1,X2,X9)
                                  & X7 = X9
                                  & m1_subset_1(X9,u1_struct_0(X1)) )
                              | ~ r2_hidden(X7,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( ~ r1_orders_2(X1,X2,X5)
                                | X4 != X5
                                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                            | ~ r2_hidden(X4,u1_struct_0(X3)) )
                          & ( ? [X5] :
                                ( r1_orders_2(X1,X2,X5)
                                & X4 = X5
                                & m1_subset_1(X5,u1_struct_0(X1)) )
                            | r2_hidden(X4,u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X4] :
                            ( ( r2_hidden(X4,u1_struct_0(X3))
                              | ! [X5] :
                                  ( ~ r1_orders_2(X1,X2,X5)
                                  | X4 != X5
                                  | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                            & ( ? [X5] :
                                  ( r1_orders_2(X1,X2,X5)
                                  & X4 = X5
                                  & m1_subset_1(X5,u1_struct_0(X1)) )
                              | ~ r2_hidden(X4,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( ~ r1_orders_2(X1,X2,X5)
                                | X4 != X5
                                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                            | ~ r2_hidden(X4,u1_struct_0(X3)) )
                          & ( ? [X5] :
                                ( r1_orders_2(X1,X2,X5)
                                & X4 = X5
                                & m1_subset_1(X5,u1_struct_0(X1)) )
                            | r2_hidden(X4,u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X4] :
                            ( ( r2_hidden(X4,u1_struct_0(X3))
                              | ! [X5] :
                                  ( ~ r1_orders_2(X1,X2,X5)
                                  | X4 != X5
                                  | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                            & ( ? [X5] :
                                  ( r1_orders_2(X1,X2,X5)
                                  & X4 = X5
                                  & m1_subset_1(X5,u1_struct_0(X1)) )
                              | ~ r2_hidden(X4,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X0)
                    & v6_waybel_0(X3,X0) )
                 => ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_waybel_9)).

fof(f1102,plain,
    ( ! [X2] :
        ( r2_hidden(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | ~ r2_hidden(X2,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))) )
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1101,f559])).

fof(f559,plain,
    ( v1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_37 ),
    inference(avatar_component_clause,[],[f557])).

fof(f557,plain,
    ( spl11_37
  <=> v1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_37])])).

fof(f1101,plain,
    ( ! [X2] :
        ( r2_hidden(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | ~ r2_hidden(X2,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | ~ v1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))) )
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1093,f880])).

fof(f880,plain,
    ( v1_funct_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f878])).

fof(f878,plain,
    ( spl11_52
  <=> v1_funct_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f1093,plain,
    ( ! [X2] :
        ( r2_hidden(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | ~ r2_hidden(X2,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | ~ v1_funct_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
        | ~ v1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))) )
    | ~ spl11_56 ),
    inference(superposition,[],[f155,f1034])).

fof(f1034,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_56 ),
    inference(avatar_component_clause,[],[f1032])).

fof(f1032,plain,
    ( spl11_56
  <=> u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f155,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK10(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK10(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK8(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK8(X0,X1),X1) )
              & ( ( sK8(X0,X1) = k1_funct_1(X0,sK9(X0,X1))
                  & r2_hidden(sK9(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK8(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK10(X0,X5)) = X5
                    & r2_hidden(sK10(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f77,f80,f79,f78])).

fof(f78,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK8(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK8(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK8(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK8(X0,X1) = k1_funct_1(X0,sK9(X0,X1))
        & r2_hidden(sK9(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK10(X0,X5)) = X5
        & r2_hidden(sK10(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f1164,plain,
    ( ! [X1] :
        ( r1_orders_2(sK1,sK2,sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X1)))
        | ~ r2_hidden(X1,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))) )
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1163,f217])).

fof(f1163,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | r1_orders_2(sK1,sK2,sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X1)))
        | v2_struct_0(sK0) )
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_11
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1162,f212])).

fof(f1162,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | r1_orders_2(sK1,sK2,sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X1)))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1161,f207])).

fof(f1161,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | r1_orders_2(sK1,sK2,sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X1)))
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1160,f192])).

fof(f1160,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | r1_orders_2(sK1,sK2,sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X1)))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_6
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1152,f187])).

fof(f1152,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | r1_orders_2(sK1,sK2,sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X1)))
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(resolution,[],[f1102,f431])).

fof(f431,plain,(
    ! [X2,X0,X7,X1] :
      ( ~ r2_hidden(X7,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | r1_orders_2(X1,X2,sK7(X1,X2,X7))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f430,f121])).

fof(f430,plain,(
    ! [X2,X0,X7,X1] :
      ( r1_orders_2(X1,X2,sK7(X1,X2,X7))
      | ~ r2_hidden(X7,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f149,f122])).

fof(f149,plain,(
    ! [X2,X0,X7,X1] :
      ( r1_orders_2(X1,X2,sK7(X1,X2,X7))
      | ~ r2_hidden(X7,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( r1_orders_2(X1,X2,sK7(X1,X2,X7))
      | ~ r2_hidden(X7,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f2105,plain,
    ( ! [X0] :
        ( sK3 != X0
        | ~ r1_orders_2(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0))
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_22
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56
    | spl11_68
    | spl11_69 ),
    inference(subsumption_resolution,[],[f2098,f1246])).

fof(f1246,plain,
    ( ! [X1] :
        ( m1_subset_1(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X1),u1_struct_0(sK1))
        | ~ r2_hidden(X1,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))) )
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(duplicate_literal_removal,[],[f1243])).

fof(f1243,plain,
    ( ! [X1] :
        ( m1_subset_1(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X1),u1_struct_0(sK1))
        | ~ r2_hidden(X1,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | ~ r2_hidden(X1,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))) )
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(superposition,[],[f1159,f1169])).

fof(f1159,plain,
    ( ! [X0] :
        ( m1_subset_1(sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)),u1_struct_0(sK1))
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))) )
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1158,f217])).

fof(f1158,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | m1_subset_1(sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_11
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1157,f212])).

fof(f1157,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | m1_subset_1(sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)),u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1156,f207])).

fof(f1156,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | m1_subset_1(sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1155,f192])).

fof(f1155,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | m1_subset_1(sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)),u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_6
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1151,f187])).

fof(f1151,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | m1_subset_1(sK7(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56 ),
    inference(resolution,[],[f1102,f435])).

fof(f435,plain,(
    ! [X2,X0,X7,X1] :
      ( ~ r2_hidden(X7,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | m1_subset_1(sK7(X1,X2,X7),u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f434,f121])).

fof(f434,plain,(
    ! [X2,X0,X7,X1] :
      ( m1_subset_1(sK7(X1,X2,X7),u1_struct_0(X1))
      | ~ r2_hidden(X7,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f151,f122])).

fof(f151,plain,(
    ! [X2,X0,X7,X1] :
      ( m1_subset_1(sK7(X1,X2,X7),u1_struct_0(X1))
      | ~ r2_hidden(X7,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( m1_subset_1(sK7(X1,X2,X7),u1_struct_0(X1))
      | ~ r2_hidden(X7,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f2098,plain,
    ( ! [X0] :
        ( sK3 != X0
        | ~ m1_subset_1(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK2,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0))
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_22
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56
    | spl11_68
    | spl11_69 ),
    inference(superposition,[],[f167,f2096])).

fof(f2096,plain,
    ( ! [X0] :
        ( k2_waybel_0(sK0,sK1,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)) = X0
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))) )
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_22
    | ~ spl11_37
    | ~ spl11_52
    | ~ spl11_56
    | spl11_68
    | spl11_69 ),
    inference(subsumption_resolution,[],[f2095,f1246])).

fof(f2095,plain,
    ( ! [X0] :
        ( k2_waybel_0(sK0,sK1,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)) = X0
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | ~ m1_subset_1(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0),u1_struct_0(sK1)) )
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_22
    | ~ spl11_37
    | ~ spl11_52
    | spl11_68
    | spl11_69 ),
    inference(subsumption_resolution,[],[f2094,f207])).

fof(f2094,plain,
    ( ! [X0] :
        ( k2_waybel_0(sK0,sK1,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)) = X0
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | ~ m1_subset_1(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0),u1_struct_0(sK1))
        | v2_struct_0(sK1) )
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_11
    | spl11_12
    | ~ spl11_22
    | ~ spl11_37
    | ~ spl11_52
    | spl11_68
    | spl11_69 ),
    inference(subsumption_resolution,[],[f2093,f197])).

fof(f197,plain,
    ( v7_waybel_0(sK1)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl11_8
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f2093,plain,
    ( ! [X0] :
        ( k2_waybel_0(sK0,sK1,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)) = X0
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | ~ m1_subset_1(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0),u1_struct_0(sK1))
        | ~ v7_waybel_0(sK1)
        | v2_struct_0(sK1) )
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_11
    | spl11_12
    | ~ spl11_22
    | ~ spl11_37
    | ~ spl11_52
    | spl11_68
    | spl11_69 ),
    inference(subsumption_resolution,[],[f2092,f192])).

fof(f2092,plain,
    ( ! [X0] :
        ( k2_waybel_0(sK0,sK1,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)) = X0
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | ~ m1_subset_1(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0),u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | v2_struct_0(sK1) )
    | ~ spl11_6
    | ~ spl11_11
    | spl11_12
    | ~ spl11_22
    | ~ spl11_37
    | ~ spl11_52
    | spl11_68
    | spl11_69 ),
    inference(subsumption_resolution,[],[f2091,f187])).

fof(f2091,plain,
    ( ! [X0] :
        ( k2_waybel_0(sK0,sK1,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)) = X0
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | ~ m1_subset_1(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | v2_struct_0(sK1) )
    | ~ spl11_11
    | spl11_12
    | ~ spl11_22
    | ~ spl11_37
    | ~ spl11_52
    | spl11_68
    | spl11_69 ),
    inference(subsumption_resolution,[],[f2090,f1666])).

fof(f1666,plain,
    ( ~ v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | spl11_68 ),
    inference(avatar_component_clause,[],[f1665])).

fof(f1665,plain,
    ( spl11_68
  <=> v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_68])])).

fof(f2090,plain,
    ( ! [X0] :
        ( k2_waybel_0(sK0,sK1,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)) = X0
        | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | ~ m1_subset_1(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | v2_struct_0(sK1) )
    | ~ spl11_11
    | spl11_12
    | ~ spl11_22
    | ~ spl11_37
    | ~ spl11_52
    | spl11_69 ),
    inference(subsumption_resolution,[],[f2089,f217])).

fof(f2089,plain,
    ( ! [X0] :
        ( k2_waybel_0(sK0,sK1,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)) = X0
        | v2_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | ~ m1_subset_1(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | v2_struct_0(sK1) )
    | ~ spl11_11
    | ~ spl11_22
    | ~ spl11_37
    | ~ spl11_52
    | spl11_69 ),
    inference(subsumption_resolution,[],[f2088,f212])).

fof(f2088,plain,
    ( ! [X0] :
        ( k2_waybel_0(sK0,sK1,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)) = X0
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | ~ m1_subset_1(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | v2_struct_0(sK1) )
    | ~ spl11_22
    | ~ spl11_37
    | ~ spl11_52
    | spl11_69 ),
    inference(subsumption_resolution,[],[f2087,f1670])).

fof(f1670,plain,
    ( ~ v2_struct_0(k4_waybel_9(sK0,sK1,sK2))
    | spl11_69 ),
    inference(avatar_component_clause,[],[f1669])).

fof(f1669,plain,
    ( spl11_69
  <=> v2_struct_0(k4_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_69])])).

fof(f2087,plain,
    ( ! [X0] :
        ( k2_waybel_0(sK0,sK1,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)) = X0
        | v2_struct_0(k4_waybel_9(sK0,sK1,sK2))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | ~ m1_subset_1(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | v2_struct_0(sK1) )
    | ~ spl11_22
    | ~ spl11_37
    | ~ spl11_52 ),
    inference(duplicate_literal_removal,[],[f2082])).

fof(f2082,plain,
    ( ! [X0] :
        ( k2_waybel_0(sK0,sK1,sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0)) = X0
        | v2_struct_0(k4_waybel_9(sK0,sK1,sK2))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | ~ m1_subset_1(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | v2_struct_0(sK1)
        | ~ r2_hidden(X0,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))) )
    | ~ spl11_22
    | ~ spl11_37
    | ~ spl11_52 ),
    inference(resolution,[],[f1223,f923])).

fof(f923,plain,
    ( ! [X1] :
        ( m1_subset_1(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | ~ r2_hidden(X1,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))) )
    | ~ spl11_22
    | ~ spl11_37
    | ~ spl11_52 ),
    inference(subsumption_resolution,[],[f922,f559])).

fof(f922,plain,
    ( ! [X1] :
        ( m1_subset_1(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | ~ r2_hidden(X1,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | ~ v1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))) )
    | ~ spl11_22
    | ~ spl11_52 ),
    inference(subsumption_resolution,[],[f919,f880])).

fof(f919,plain,
    ( ! [X1] :
        ( m1_subset_1(sK10(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),X1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | ~ r2_hidden(X1,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | ~ v1_funct_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
        | ~ v1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))) )
    | ~ spl11_22 ),
    inference(resolution,[],[f627,f155])).

fof(f627,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
        | m1_subset_1(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) )
    | ~ spl11_22 ),
    inference(resolution,[],[f354,f295])).

fof(f295,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(X3,X0)
      | ~ r2_hidden(X3,k1_relat_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_relat_1(X2))
      | m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f258,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f258,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_relset_1(X1,X2,X0))
      | m1_subset_1(X3,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f136,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f354,plain,
    ( m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl11_22
  <=> m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f1223,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK10(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),X3),u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | k2_waybel_0(X0,X1,sK10(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),X3)) = X3
      | v2_struct_0(k4_waybel_9(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ r2_hidden(X3,k2_relat_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | ~ m1_subset_1(sK10(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),X3),u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f1222,f122])).

fof(f1222,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_waybel_0(X0,X1,sK10(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),X3)) = X3
      | ~ m1_subset_1(sK10(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),X3),u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | v2_struct_0(k4_waybel_9(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ r2_hidden(X3,k2_relat_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | ~ m1_subset_1(sK10(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),X3),u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f1215])).

% (9312)Termination reason: Refutation not found, incomplete strategy
fof(f1215,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_waybel_0(X0,X1,sK10(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),X3)) = X3
      | ~ m1_subset_1(sK10(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),X3),u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | v2_struct_0(k4_waybel_9(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ r2_hidden(X3,k2_relat_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | ~ m1_subset_1(sK10(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),X3),u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(sK10(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)),X3),u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f783,f143])).

fof(f143,plain,(
    ! [X4,X2,X0,X1] :
      ( k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4) = k2_waybel_0(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_waybel_0(X0,X1,X3) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

% (9312)Memory used [KB]: 11129
% (9312)Time elapsed: 0.160 s
% (9312)------------------------------
% (9312)------------------------------
fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_waybel_0(X0,X1,X3) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_waybel_0(X0,X1,X3) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
                     => ( X3 = X4
                       => k2_waybel_0(X0,X1,X3) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_waybel_9)).

fof(f783,plain,(
    ! [X4,X5,X3] :
      ( k2_waybel_0(X3,X4,sK10(u1_waybel_0(X3,X4),X5)) = X5
      | ~ m1_subset_1(sK10(u1_waybel_0(X3,X4),X5),u1_struct_0(X4))
      | ~ l1_waybel_0(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3)
      | v1_xboole_0(u1_struct_0(X4))
      | ~ r2_hidden(X5,k2_relat_1(u1_waybel_0(X3,X4))) ) ),
    inference(subsumption_resolution,[],[f782,f277])).

fof(f277,plain,(
    ! [X8,X7] :
      ( v1_relat_1(u1_waybel_0(X8,X7))
      | ~ l1_struct_0(X8)
      | ~ l1_waybel_0(X7,X8) ) ),
    inference(subsumption_resolution,[],[f270,f139])).

fof(f139,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f270,plain,(
    ! [X8,X7] :
      ( ~ l1_waybel_0(X7,X8)
      | ~ l1_struct_0(X8)
      | v1_relat_1(u1_waybel_0(X8,X7))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))) ) ),
    inference(resolution,[],[f118,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f782,plain,(
    ! [X4,X5,X3] :
      ( k2_waybel_0(X3,X4,sK10(u1_waybel_0(X3,X4),X5)) = X5
      | ~ m1_subset_1(sK10(u1_waybel_0(X3,X4),X5),u1_struct_0(X4))
      | ~ l1_waybel_0(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3)
      | v1_xboole_0(u1_struct_0(X4))
      | ~ r2_hidden(X5,k2_relat_1(u1_waybel_0(X3,X4)))
      | ~ v1_relat_1(u1_waybel_0(X3,X4)) ) ),
    inference(subsumption_resolution,[],[f775,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f775,plain,(
    ! [X4,X5,X3] :
      ( k2_waybel_0(X3,X4,sK10(u1_waybel_0(X3,X4),X5)) = X5
      | ~ m1_subset_1(sK10(u1_waybel_0(X3,X4),X5),u1_struct_0(X4))
      | ~ l1_waybel_0(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3)
      | v1_xboole_0(u1_struct_0(X4))
      | ~ r2_hidden(X5,k2_relat_1(u1_waybel_0(X3,X4)))
      | ~ v1_funct_1(u1_waybel_0(X3,X4))
      | ~ v1_relat_1(u1_waybel_0(X3,X4)) ) ),
    inference(superposition,[],[f384,f154])).

fof(f154,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK10(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK10(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f384,plain,(
    ! [X4,X5,X3] :
      ( k1_funct_1(u1_waybel_0(X4,X3),X5) = k2_waybel_0(X4,X3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f383,f116])).

fof(f383,plain,(
    ! [X4,X5,X3] :
      ( k1_funct_1(u1_waybel_0(X4,X3),X5) = k2_waybel_0(X4,X3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | ~ v1_funct_1(u1_waybel_0(X4,X3))
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f382,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f382,plain,(
    ! [X4,X5,X3] :
      ( k1_funct_1(u1_waybel_0(X4,X3),X5) = k2_waybel_0(X4,X3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(u1_waybel_0(X4,X3),u1_struct_0(X3),u1_struct_0(X4))
      | ~ v1_funct_1(u1_waybel_0(X4,X3))
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f381,f118])).

fof(f381,plain,(
    ! [X4,X5,X3] :
      ( k1_funct_1(u1_waybel_0(X4,X3),X5) = k2_waybel_0(X4,X3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(u1_waybel_0(X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
      | ~ v1_funct_2(u1_waybel_0(X4,X3),u1_struct_0(X3),u1_struct_0(X4))
      | ~ v1_funct_1(u1_waybel_0(X4,X3))
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f378])).

fof(f378,plain,(
    ! [X4,X5,X3] :
      ( k1_funct_1(u1_waybel_0(X4,X3),X5) = k2_waybel_0(X4,X3,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(u1_waybel_0(X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
      | ~ v1_funct_2(u1_waybel_0(X4,X3),u1_struct_0(X3),u1_struct_0(X4))
      | ~ v1_funct_1(u1_waybel_0(X4,X3))
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(superposition,[],[f96,f129])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_waybel_0)).

fof(f167,plain,
    ( ! [X4] :
        ( k2_waybel_0(sK0,sK1,X4) != sK3
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK2,X4) )
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl11_2
  <=> ! [X4] :
        ( k2_waybel_0(sK0,sK1,X4) != sK3
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK2,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f2012,plain,
    ( spl11_28
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_19 ),
    inference(avatar_split_clause,[],[f2011,f254,f215,f210,f205,f200,f195,f190,f185,f455])).

fof(f200,plain,
    ( spl11_9
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f254,plain,
    ( spl11_19
  <=> r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f2011,plain,
    ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f2010,f217])).

fof(f2010,plain,
    ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f2009,f212])).

fof(f2009,plain,
    ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f2008,f207])).

fof(f2008,plain,
    ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f2007,f202])).

fof(f202,plain,
    ( v4_orders_2(sK1)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f200])).

fof(f2007,plain,
    ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f2006,f197])).

fof(f2006,plain,
    ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f2005,f192])).

fof(f2005,plain,
    ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f1990,f187])).

fof(f1990,plain,
    ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_19 ),
    inference(superposition,[],[f255,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k4_waybel_9(X0,X1,X2) = k5_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_waybel_9(X0,X1,X2) = k5_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_waybel_9(X0,X1,X2) = k5_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => k4_waybel_9(X0,X1,X2) = k5_waybel_9(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_waybel_9)).

fof(f255,plain,
    ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f254])).

fof(f1980,plain,
    ( spl11_19
    | ~ spl11_1
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f1979,f250,f162,f254])).

fof(f162,plain,
    ( spl11_1
  <=> r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f250,plain,
    ( spl11_18
  <=> m1_subset_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f1979,plain,
    ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
    | ~ spl11_1
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f1961,f251])).

fof(f251,plain,
    ( m1_subset_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f250])).

fof(f1961,plain,
    ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
    | ~ m1_subset_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | ~ spl11_1 ),
    inference(superposition,[],[f163,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f163,plain,
    ( r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f162])).

fof(f1920,plain,
    ( ~ spl11_74
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | spl11_28
    | ~ spl11_56
    | spl11_68
    | spl11_69 ),
    inference(avatar_split_clause,[],[f1919,f1669,f1665,f1032,f455,f215,f210,f205,f195,f190,f185,f180,f170,f1879])).

fof(f1879,plain,
    ( spl11_74
  <=> r2_hidden(sK4,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_74])])).

fof(f170,plain,
    ( spl11_3
  <=> sK3 = k2_waybel_0(sK0,sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f180,plain,
    ( spl11_5
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f1919,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | spl11_28
    | ~ spl11_56
    | spl11_68
    | spl11_69 ),
    inference(subsumption_resolution,[],[f1918,f187])).

fof(f1918,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | spl11_28
    | ~ spl11_56
    | spl11_68
    | spl11_69 ),
    inference(subsumption_resolution,[],[f1917,f1666])).

fof(f1917,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | spl11_28
    | ~ spl11_56
    | spl11_69 ),
    inference(subsumption_resolution,[],[f1916,f1670])).

fof(f1916,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(k4_waybel_9(sK0,sK1,sK2))
    | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | spl11_28
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1914,f457])).

fof(f457,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | spl11_28 ),
    inference(avatar_component_clause,[],[f455])).

fof(f1914,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(k4_waybel_9(sK0,sK1,sK2))
    | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_56 ),
    inference(superposition,[],[f1865,f1034])).

fof(f1865,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X0))))
        | r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X0))))
        | v2_struct_0(k4_waybel_9(sK0,sK1,X0))
        | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,X0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | spl11_10
    | ~ spl11_11
    | spl11_12 ),
    inference(subsumption_resolution,[],[f1864,f207])).

fof(f1864,plain,
    ( ! [X0] :
        ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X0))))
        | ~ r2_hidden(sK4,k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X0))))
        | v2_struct_0(k4_waybel_9(sK0,sK1,X0))
        | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,X0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(sK1) )
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_11
    | spl11_12 ),
    inference(subsumption_resolution,[],[f1863,f197])).

fof(f1863,plain,
    ( ! [X0] :
        ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X0))))
        | ~ r2_hidden(sK4,k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X0))))
        | v2_struct_0(k4_waybel_9(sK0,sK1,X0))
        | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,X0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v7_waybel_0(sK1)
        | v2_struct_0(sK1) )
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_11
    | spl11_12 ),
    inference(subsumption_resolution,[],[f1862,f192])).

fof(f1862,plain,
    ( ! [X0] :
        ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X0))))
        | ~ r2_hidden(sK4,k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X0))))
        | v2_struct_0(k4_waybel_9(sK0,sK1,X0))
        | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,X0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | v2_struct_0(sK1) )
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_11
    | spl11_12 ),
    inference(subsumption_resolution,[],[f1861,f182])).

fof(f182,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f180])).

fof(f1861,plain,
    ( ! [X0] :
        ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X0))))
        | ~ r2_hidden(sK4,k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X0))))
        | v2_struct_0(k4_waybel_9(sK0,sK1,X0))
        | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,X0)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | v2_struct_0(sK1) )
    | ~ spl11_3
    | ~ spl11_11
    | spl11_12 ),
    inference(subsumption_resolution,[],[f1860,f217])).

fof(f1860,plain,
    ( ! [X0] :
        ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X0))))
        | ~ r2_hidden(sK4,k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X0))))
        | v2_struct_0(k4_waybel_9(sK0,sK1,X0))
        | v2_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,X0)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | v2_struct_0(sK1) )
    | ~ spl11_3
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f1853,f212])).

fof(f1853,plain,
    ( ! [X0] :
        ( r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X0))))
        | ~ r2_hidden(sK4,k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,X0))))
        | v2_struct_0(k4_waybel_9(sK0,sK1,X0))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,X0)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | v2_struct_0(sK1) )
    | ~ spl11_3 ),
    inference(superposition,[],[f1210,f172])).

fof(f172,plain,
    ( sK3 = k2_waybel_0(sK0,sK1,sK4)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f170])).

fof(f1210,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X3),k2_relat_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | ~ r2_hidden(X3,k1_relat_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | v2_struct_0(k4_waybel_9(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f1209,f122])).

fof(f1209,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X3),k2_relat_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | ~ r2_hidden(X3,k1_relat_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | v2_struct_0(k4_waybel_9(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f1208,f284])).

fof(f284,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(u1_waybel_0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f268,f107])).

fof(f268,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k1_relat_1(u1_waybel_0(X3,X2)),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_struct_0(X3)
      | ~ l1_waybel_0(X2,X3) ) ),
    inference(resolution,[],[f118,f261])).

fof(f261,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f136,f137])).

fof(f1208,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X3),k2_relat_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | ~ r2_hidden(X3,k1_relat_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | v2_struct_0(k4_waybel_9(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f1207])).

fof(f1207,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X3),k2_relat_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | ~ r2_hidden(X3,k1_relat_1(u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | v2_struct_0(k4_waybel_9(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f794,f143])).

fof(f794,plain,(
    ! [X8,X7,X9] :
      ( r2_hidden(k2_waybel_0(X7,X8,X9),k2_relat_1(u1_waybel_0(X7,X8)))
      | ~ r2_hidden(X9,k1_relat_1(u1_waybel_0(X7,X8)))
      | ~ l1_waybel_0(X8,X7)
      | v2_struct_0(X8)
      | ~ l1_struct_0(X7)
      | v2_struct_0(X7)
      | v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(subsumption_resolution,[],[f793,f277])).

fof(f793,plain,(
    ! [X8,X7,X9] :
      ( r2_hidden(k2_waybel_0(X7,X8,X9),k2_relat_1(u1_waybel_0(X7,X8)))
      | ~ r2_hidden(X9,k1_relat_1(u1_waybel_0(X7,X8)))
      | ~ v1_relat_1(u1_waybel_0(X7,X8))
      | ~ l1_waybel_0(X8,X7)
      | v2_struct_0(X8)
      | ~ l1_struct_0(X7)
      | v2_struct_0(X7)
      | v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(subsumption_resolution,[],[f792,f116])).

fof(f792,plain,(
    ! [X8,X7,X9] :
      ( r2_hidden(k2_waybel_0(X7,X8,X9),k2_relat_1(u1_waybel_0(X7,X8)))
      | ~ r2_hidden(X9,k1_relat_1(u1_waybel_0(X7,X8)))
      | ~ v1_funct_1(u1_waybel_0(X7,X8))
      | ~ v1_relat_1(u1_waybel_0(X7,X8))
      | ~ l1_waybel_0(X8,X7)
      | v2_struct_0(X8)
      | ~ l1_struct_0(X7)
      | v2_struct_0(X7)
      | v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(subsumption_resolution,[],[f779,f284])).

fof(f779,plain,(
    ! [X8,X7,X9] :
      ( r2_hidden(k2_waybel_0(X7,X8,X9),k2_relat_1(u1_waybel_0(X7,X8)))
      | ~ r2_hidden(X9,k1_relat_1(u1_waybel_0(X7,X8)))
      | ~ v1_funct_1(u1_waybel_0(X7,X8))
      | ~ v1_relat_1(u1_waybel_0(X7,X8))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_waybel_0(X8,X7)
      | v2_struct_0(X8)
      | ~ l1_struct_0(X7)
      | v2_struct_0(X7)
      | v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(superposition,[],[f153,f384])).

fof(f153,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f152])).

fof(f152,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f1895,plain,
    ( ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | spl11_74 ),
    inference(avatar_contradiction_clause,[],[f1894])).

fof(f1894,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | spl11_74 ),
    inference(subsumption_resolution,[],[f1893,f217])).

fof(f1893,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_11
    | spl11_74 ),
    inference(subsumption_resolution,[],[f1892,f212])).

fof(f1892,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | spl11_74 ),
    inference(subsumption_resolution,[],[f1891,f207])).

fof(f1891,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_74 ),
    inference(subsumption_resolution,[],[f1890,f192])).

fof(f1890,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | spl11_74 ),
    inference(subsumption_resolution,[],[f1889,f187])).

fof(f1889,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_4
    | ~ spl11_5
    | spl11_74 ),
    inference(subsumption_resolution,[],[f1888,f182])).

fof(f1888,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_4
    | spl11_74 ),
    inference(subsumption_resolution,[],[f1886,f177])).

fof(f177,plain,
    ( r1_orders_2(sK1,sK2,sK4)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl11_4
  <=> r1_orders_2(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f1886,plain,
    ( ~ r1_orders_2(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl11_74 ),
    inference(resolution,[],[f1881,f437])).

fof(f437,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(X8,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ r1_orders_2(X1,X2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f436,f121])).

fof(f436,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(X8,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ r1_orders_2(X1,X2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f148,f122])).

fof(f148,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(X8,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ r1_orders_2(X1,X2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f147])).

fof(f147,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,u1_struct_0(X3))
      | ~ r1_orders_2(X1,X2,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,u1_struct_0(X3))
      | ~ r1_orders_2(X1,X2,X8)
      | X7 != X8
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f1881,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | spl11_74 ),
    inference(avatar_component_clause,[],[f1879])).

fof(f1835,plain,
    ( ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_69 ),
    inference(avatar_contradiction_clause,[],[f1834])).

fof(f1834,plain,
    ( $false
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_69 ),
    inference(subsumption_resolution,[],[f1833,f187])).

fof(f1833,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_69 ),
    inference(subsumption_resolution,[],[f1832,f217])).

fof(f1832,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | ~ spl11_69 ),
    inference(subsumption_resolution,[],[f1831,f212])).

fof(f1831,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_69 ),
    inference(subsumption_resolution,[],[f1830,f207])).

fof(f1830,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_69 ),
    inference(subsumption_resolution,[],[f1829,f202])).

fof(f1829,plain,
    ( ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_69 ),
    inference(subsumption_resolution,[],[f1828,f197])).

fof(f1828,plain,
    ( ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_7
    | ~ spl11_69 ),
    inference(subsumption_resolution,[],[f1826,f192])).

fof(f1826,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_69 ),
    inference(resolution,[],[f1671,f620])).

fof(f620,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k4_waybel_9(X0,X1,X2))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f619])).

fof(f619,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k4_waybel_9(X0,X1,X2))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f322,f94])).

fof(f322,plain,(
    ! [X10,X11,X9] :
      ( ~ v2_struct_0(k5_waybel_9(X11,X10,X9))
      | ~ l1_waybel_0(X10,X11)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | ~ l1_struct_0(X11)
      | v2_struct_0(X11)
      | ~ m1_subset_1(X9,u1_struct_0(X10)) ) ),
    inference(duplicate_literal_removal,[],[f321])).

fof(f321,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ l1_waybel_0(X10,X11)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | ~ l1_struct_0(X11)
      | v2_struct_0(X11)
      | ~ v2_struct_0(k5_waybel_9(X11,X10,X9))
      | ~ l1_waybel_0(X10,X11)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | ~ l1_struct_0(X11)
      | v2_struct_0(X11) ) ),
    inference(resolution,[],[f120,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | ~ v2_struct_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
        & v6_waybel_0(k5_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
        & v6_waybel_0(k5_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
        & v6_waybel_0(k5_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_9)).

fof(f1671,plain,
    ( v2_struct_0(k4_waybel_9(sK0,sK1,sK2))
    | ~ spl11_69 ),
    inference(avatar_component_clause,[],[f1669])).

fof(f1751,plain,
    ( ~ spl11_68
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | spl11_65 ),
    inference(avatar_split_clause,[],[f1750,f1649,f215,f210,f205,f200,f195,f190,f185,f1665])).

fof(f1649,plain,
    ( spl11_65
  <=> v1_xboole_0(u1_struct_0(k5_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_65])])).

fof(f1750,plain,
    ( ~ v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | spl11_65 ),
    inference(subsumption_resolution,[],[f1749,f217])).

fof(f1749,plain,
    ( ~ v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_65 ),
    inference(subsumption_resolution,[],[f1748,f212])).

fof(f1748,plain,
    ( ~ v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | spl11_65 ),
    inference(subsumption_resolution,[],[f1747,f207])).

fof(f1747,plain,
    ( ~ v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_65 ),
    inference(subsumption_resolution,[],[f1746,f202])).

fof(f1746,plain,
    ( ~ v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_65 ),
    inference(subsumption_resolution,[],[f1745,f197])).

fof(f1745,plain,
    ( ~ v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | spl11_65 ),
    inference(subsumption_resolution,[],[f1744,f192])).

fof(f1744,plain,
    ( ~ v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | spl11_65 ),
    inference(subsumption_resolution,[],[f1743,f187])).

fof(f1743,plain,
    ( ~ v1_xboole_0(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl11_65 ),
    inference(superposition,[],[f1650,f94])).

fof(f1650,plain,
    ( ~ v1_xboole_0(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
    | spl11_65 ),
    inference(avatar_component_clause,[],[f1649])).

fof(f1728,plain,
    ( ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_66 ),
    inference(avatar_contradiction_clause,[],[f1727])).

fof(f1727,plain,
    ( $false
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f1726,f187])).

fof(f1726,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f1725,f217])).

fof(f1725,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f1724,f212])).

fof(f1724,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f1723,f207])).

fof(f1723,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f1722,f202])).

fof(f1722,plain,
    ( ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f1721,f197])).

fof(f1721,plain,
    ( ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_7
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f1718,f192])).

fof(f1718,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_66 ),
    inference(resolution,[],[f1655,f322])).

fof(f1655,plain,
    ( v2_struct_0(k5_waybel_9(sK0,sK1,sK2))
    | ~ spl11_66 ),
    inference(avatar_component_clause,[],[f1653])).

fof(f1653,plain,
    ( spl11_66
  <=> v2_struct_0(k5_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_66])])).

fof(f1702,plain,
    ( spl11_66
    | ~ spl11_25
    | ~ spl11_65 ),
    inference(avatar_split_clause,[],[f1701,f1649,f401,f1653])).

fof(f401,plain,
    ( spl11_25
  <=> l1_struct_0(k5_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f1701,plain,
    ( v2_struct_0(k5_waybel_9(sK0,sK1,sK2))
    | ~ spl11_25
    | ~ spl11_65 ),
    inference(subsumption_resolution,[],[f1699,f403])).

fof(f403,plain,
    ( l1_struct_0(k5_waybel_9(sK0,sK1,sK2))
    | ~ spl11_25 ),
    inference(avatar_component_clause,[],[f401])).

fof(f1699,plain,
    ( ~ l1_struct_0(k5_waybel_9(sK0,sK1,sK2))
    | v2_struct_0(k5_waybel_9(sK0,sK1,sK2))
    | ~ spl11_65 ),
    inference(resolution,[],[f1651,f123])).

fof(f123,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f1651,plain,
    ( v1_xboole_0(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_65 ),
    inference(avatar_component_clause,[],[f1649])).

fof(f1035,plain,
    ( spl11_56
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_53 ),
    inference(avatar_split_clause,[],[f1030,f955,f215,f210,f205,f200,f195,f190,f185,f1032])).

fof(f955,plain,
    ( spl11_53
  <=> u1_struct_0(k5_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_53])])).

fof(f1030,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_53 ),
    inference(subsumption_resolution,[],[f1029,f217])).

fof(f1029,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | ~ spl11_53 ),
    inference(subsumption_resolution,[],[f1028,f212])).

fof(f1028,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_53 ),
    inference(subsumption_resolution,[],[f1027,f207])).

fof(f1027,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_53 ),
    inference(subsumption_resolution,[],[f1026,f202])).

fof(f1026,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_53 ),
    inference(subsumption_resolution,[],[f1025,f197])).

fof(f1025,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_53 ),
    inference(subsumption_resolution,[],[f1024,f192])).

fof(f1024,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_53 ),
    inference(subsumption_resolution,[],[f1013,f187])).

fof(f1013,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_53 ),
    inference(superposition,[],[f957,f94])).

fof(f957,plain,
    ( u1_struct_0(k5_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_53 ),
    inference(avatar_component_clause,[],[f955])).

fof(f960,plain,
    ( spl11_53
    | ~ spl11_18
    | ~ spl11_29 ),
    inference(avatar_split_clause,[],[f959,f471,f250,f955])).

fof(f471,plain,
    ( spl11_29
  <=> u1_struct_0(k5_waybel_9(sK0,sK1,sK2)) = k1_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f959,plain,
    ( u1_struct_0(k5_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_18
    | ~ spl11_29 ),
    inference(subsumption_resolution,[],[f942,f251])).

fof(f942,plain,
    ( u1_struct_0(k5_waybel_9(sK0,sK1,sK2)) = k1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ m1_subset_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | ~ spl11_29 ),
    inference(superposition,[],[f137,f473])).

fof(f473,plain,
    ( u1_struct_0(k5_waybel_9(sK0,sK1,sK2)) = k1_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f471])).

fof(f881,plain,
    ( spl11_52
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_47 ),
    inference(avatar_split_clause,[],[f876,f815,f215,f210,f205,f200,f195,f190,f185,f878])).

fof(f815,plain,
    ( spl11_47
  <=> v1_funct_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_47])])).

fof(f876,plain,
    ( v1_funct_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f875,f217])).

fof(f875,plain,
    ( v1_funct_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f874,f212])).

fof(f874,plain,
    ( v1_funct_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f873,f207])).

fof(f873,plain,
    ( v1_funct_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f872,f202])).

fof(f872,plain,
    ( v1_funct_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f871,f197])).

fof(f871,plain,
    ( v1_funct_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f870,f192])).

fof(f870,plain,
    ( v1_funct_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f869,f187])).

fof(f869,plain,
    ( v1_funct_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_47 ),
    inference(superposition,[],[f816,f94])).

fof(f816,plain,
    ( v1_funct_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_47 ),
    inference(avatar_component_clause,[],[f815])).

fof(f859,plain,
    ( ~ spl11_11
    | ~ spl11_20
    | spl11_47 ),
    inference(avatar_contradiction_clause,[],[f858])).

fof(f858,plain,
    ( $false
    | ~ spl11_11
    | ~ spl11_20
    | spl11_47 ),
    inference(subsumption_resolution,[],[f857,f212])).

fof(f857,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl11_20
    | spl11_47 ),
    inference(subsumption_resolution,[],[f854,f274])).

fof(f274,plain,
    ( l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl11_20
  <=> l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f854,plain,
    ( ~ l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
    | ~ l1_struct_0(sK0)
    | spl11_47 ),
    inference(resolution,[],[f817,f116])).

fof(f817,plain,
    ( ~ v1_funct_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | spl11_47 ),
    inference(avatar_component_clause,[],[f815])).

fof(f764,plain,
    ( spl11_22
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f763,f250,f215,f210,f205,f200,f195,f190,f185,f353])).

fof(f763,plain,
    ( m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f762,f217])).

fof(f762,plain,
    ( m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f761,f212])).

fof(f761,plain,
    ( m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f760,f207])).

fof(f760,plain,
    ( m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f759,f202])).

fof(f759,plain,
    ( m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f758,f197])).

fof(f758,plain,
    ( m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f757,f192])).

fof(f757,plain,
    ( m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f754,f187])).

fof(f754,plain,
    ( m1_subset_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_18 ),
    inference(superposition,[],[f251,f94])).

fof(f756,plain,
    ( spl11_29
    | ~ spl11_31
    | ~ spl11_18
    | spl11_30 ),
    inference(avatar_split_clause,[],[f755,f475,f250,f479,f471])).

fof(f479,plain,
    ( spl11_31
  <=> v1_funct_2(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f475,plain,
    ( spl11_30
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f755,plain,
    ( ~ v1_funct_2(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))
    | u1_struct_0(k5_waybel_9(sK0,sK1,sK2)) = k1_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_18
    | spl11_30 ),
    inference(subsumption_resolution,[],[f749,f476])).

fof(f476,plain,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | spl11_30 ),
    inference(avatar_component_clause,[],[f475])).

fof(f749,plain,
    ( ~ v1_funct_2(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(k5_waybel_9(sK0,sK1,sK2)) = k1_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_18 ),
    inference(resolution,[],[f251,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f730,plain,
    ( ~ spl11_11
    | spl11_12
    | ~ spl11_15
    | ~ spl11_30 ),
    inference(avatar_contradiction_clause,[],[f729])).

fof(f729,plain,
    ( $false
    | ~ spl11_11
    | spl11_12
    | ~ spl11_15
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f728,f217])).

fof(f728,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_11
    | ~ spl11_15
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f727,f212])).

fof(f727,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_15
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f672,f233])).

fof(f233,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl11_15
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f672,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_30 ),
    inference(superposition,[],[f123,f477])).

fof(f477,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f475])).

fof(f570,plain,
    ( ~ spl11_11
    | ~ spl11_20
    | spl11_31 ),
    inference(avatar_contradiction_clause,[],[f569])).

fof(f569,plain,
    ( $false
    | ~ spl11_11
    | ~ spl11_20
    | spl11_31 ),
    inference(subsumption_resolution,[],[f568,f212])).

fof(f568,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl11_20
    | spl11_31 ),
    inference(subsumption_resolution,[],[f565,f274])).

fof(f565,plain,
    ( ~ l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
    | ~ l1_struct_0(sK0)
    | spl11_31 ),
    inference(resolution,[],[f481,f117])).

fof(f481,plain,
    ( ~ v1_funct_2(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))
    | spl11_31 ),
    inference(avatar_component_clause,[],[f479])).

fof(f560,plain,
    ( spl11_37
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_35 ),
    inference(avatar_split_clause,[],[f555,f499,f215,f210,f205,f200,f195,f190,f185,f557])).

fof(f499,plain,
    ( spl11_35
  <=> v1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f555,plain,
    ( v1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f554,f217])).

fof(f554,plain,
    ( v1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f553,f212])).

fof(f553,plain,
    ( v1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f552,f207])).

fof(f552,plain,
    ( v1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f551,f202])).

fof(f551,plain,
    ( v1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f550,f197])).

fof(f550,plain,
    ( v1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f549,f192])).

fof(f549,plain,
    ( v1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f548,f187])).

fof(f548,plain,
    ( v1_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_35 ),
    inference(superposition,[],[f501,f94])).

fof(f501,plain,
    ( v1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_35 ),
    inference(avatar_component_clause,[],[f499])).

fof(f502,plain,
    ( spl11_35
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f497,f250,f499])).

fof(f497,plain,
    ( v1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f468,f139])).

fof(f468,plain,
    ( v1_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0)))
    | ~ spl11_18 ),
    inference(resolution,[],[f251,f138])).

fof(f458,plain,
    ( ~ spl11_28
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | spl11_19 ),
    inference(avatar_split_clause,[],[f453,f254,f215,f210,f205,f200,f195,f190,f185,f455])).

fof(f453,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | spl11_19 ),
    inference(subsumption_resolution,[],[f452,f217])).

fof(f452,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_19 ),
    inference(subsumption_resolution,[],[f451,f212])).

fof(f451,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | spl11_19 ),
    inference(subsumption_resolution,[],[f450,f207])).

fof(f450,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_19 ),
    inference(subsumption_resolution,[],[f449,f202])).

fof(f449,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_19 ),
    inference(subsumption_resolution,[],[f448,f197])).

fof(f448,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | spl11_19 ),
    inference(subsumption_resolution,[],[f447,f192])).

fof(f447,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | spl11_19 ),
    inference(subsumption_resolution,[],[f446,f187])).

fof(f446,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2))))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl11_19 ),
    inference(superposition,[],[f256,f94])).

fof(f256,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
    | spl11_19 ),
    inference(avatar_component_clause,[],[f254])).

fof(f404,plain,
    ( spl11_25
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f398,f392,f401])).

fof(f392,plain,
    ( spl11_24
  <=> l1_orders_2(k5_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f398,plain,
    ( l1_struct_0(k5_waybel_9(sK0,sK1,sK2))
    | ~ spl11_24 ),
    inference(resolution,[],[f394,f141])).

fof(f141,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f394,plain,
    ( l1_orders_2(k5_waybel_9(sK0,sK1,sK2))
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f392])).

fof(f395,plain,
    ( spl11_24
    | ~ spl11_11
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f390,f273,f210,f392])).

fof(f390,plain,
    ( l1_orders_2(k5_waybel_9(sK0,sK1,sK2))
    | ~ spl11_11
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f388,f212])).

fof(f388,plain,
    ( l1_orders_2(k5_waybel_9(sK0,sK1,sK2))
    | ~ l1_struct_0(sK0)
    | ~ spl11_20 ),
    inference(resolution,[],[f274,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | l1_orders_2(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f377,plain,
    ( ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | spl11_21 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | spl11_21 ),
    inference(subsumption_resolution,[],[f375,f217])).

fof(f375,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | ~ spl11_11
    | spl11_21 ),
    inference(subsumption_resolution,[],[f374,f212])).

fof(f374,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | spl11_10
    | spl11_21 ),
    inference(subsumption_resolution,[],[f373,f207])).

fof(f373,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | spl11_21 ),
    inference(subsumption_resolution,[],[f372,f192])).

fof(f372,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | spl11_21 ),
    inference(subsumption_resolution,[],[f370,f187])).

fof(f370,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl11_21 ),
    inference(resolution,[],[f343,f122])).

fof(f343,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | spl11_21 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl11_21
  <=> l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f344,plain,
    ( ~ spl11_21
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | spl11_20 ),
    inference(avatar_split_clause,[],[f339,f273,f215,f210,f205,f200,f195,f190,f185,f341])).

fof(f339,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_12
    | spl11_20 ),
    inference(subsumption_resolution,[],[f338,f217])).

fof(f338,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | ~ spl11_11
    | spl11_20 ),
    inference(subsumption_resolution,[],[f337,f212])).

fof(f337,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_10
    | spl11_20 ),
    inference(subsumption_resolution,[],[f336,f207])).

fof(f336,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_20 ),
    inference(subsumption_resolution,[],[f335,f202])).

fof(f335,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_20 ),
    inference(subsumption_resolution,[],[f334,f197])).

fof(f334,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | spl11_20 ),
    inference(subsumption_resolution,[],[f333,f192])).

fof(f333,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | spl11_20 ),
    inference(subsumption_resolution,[],[f326,f187])).

fof(f326,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl11_20 ),
    inference(superposition,[],[f275,f94])).

fof(f275,plain,
    ( ~ l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
    | spl11_20 ),
    inference(avatar_component_clause,[],[f273])).

fof(f276,plain,
    ( ~ spl11_20
    | ~ spl11_11
    | spl11_18 ),
    inference(avatar_split_clause,[],[f271,f250,f210,f273])).

fof(f271,plain,
    ( ~ l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
    | ~ spl11_11
    | spl11_18 ),
    inference(subsumption_resolution,[],[f266,f212])).

fof(f266,plain,
    ( ~ l1_waybel_0(k5_waybel_9(sK0,sK1,sK2),sK0)
    | ~ l1_struct_0(sK0)
    | spl11_18 ),
    inference(resolution,[],[f118,f252])).

fof(f252,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | spl11_18 ),
    inference(avatar_component_clause,[],[f250])).

fof(f257,plain,
    ( ~ spl11_18
    | ~ spl11_19
    | spl11_1 ),
    inference(avatar_split_clause,[],[f248,f162,f254,f250])).

fof(f248,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
    | ~ m1_subset_1(u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0))))
    | spl11_1 ),
    inference(superposition,[],[f164,f115])).

fof(f164,plain,
    ( ~ r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2))))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f162])).

fof(f234,plain,
    ( spl11_15
    | ~ spl11_13
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f229,f225,f220,f231])).

fof(f220,plain,
    ( spl11_13
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f225,plain,
    ( spl11_14
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f229,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl11_13
    | ~ spl11_14 ),
    inference(backward_demodulation,[],[f222,f227])).

fof(f227,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f225])).

fof(f222,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f220])).

fof(f228,plain,(
    spl11_14 ),
    inference(avatar_split_clause,[],[f142,f225])).

fof(f142,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f223,plain,(
    spl11_13 ),
    inference(avatar_split_clause,[],[f140,f220])).

fof(f140,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f218,plain,(
    ~ spl11_12 ),
    inference(avatar_split_clause,[],[f83,f215])).

fof(f83,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,
    ( ( ! [X4] :
          ( k2_waybel_0(sK0,sK1,X4) != sK3
          | ~ r1_orders_2(sK1,sK2,X4)
          | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
      | ~ r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) )
    & ( ( sK3 = k2_waybel_0(sK0,sK1,sK4)
        & r1_orders_2(sK1,sK2,sK4)
        & m1_subset_1(sK4,u1_struct_0(sK1)) )
      | r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f62,f67,f66,f65,f64,f63])).

fof(f63,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( k2_waybel_0(X0,X1,X4) != X3
                          | ~ r1_orders_2(X1,X2,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                      | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) )
                    & ( ? [X5] :
                          ( k2_waybel_0(X0,X1,X5) = X3
                          & r1_orders_2(X1,X2,X5)
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) ) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( k2_waybel_0(sK0,X1,X4) != X3
                        | ~ r1_orders_2(X1,X2,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,X1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,X1,X2)))) )
                  & ( ? [X5] :
                        ( k2_waybel_0(sK0,X1,X5) = X3
                        & r1_orders_2(X1,X2,X5)
                        & m1_subset_1(X5,u1_struct_0(X1)) )
                    | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,X1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,X1,X2)))) ) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( k2_waybel_0(sK0,X1,X4) != X3
                      | ~ r1_orders_2(X1,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,X1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,X1,X2)))) )
                & ( ? [X5] :
                      ( k2_waybel_0(sK0,X1,X5) = X3
                      & r1_orders_2(X1,X2,X5)
                      & m1_subset_1(X5,u1_struct_0(X1)) )
                  | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,X1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,X1,X2)))) ) )
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( k2_waybel_0(sK0,sK1,X4) != X3
                    | ~ r1_orders_2(sK1,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
                | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,X2)))) )
              & ( ? [X5] :
                    ( k2_waybel_0(sK0,sK1,X5) = X3
                    & r1_orders_2(sK1,X2,X5)
                    & m1_subset_1(X5,u1_struct_0(sK1)) )
                | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,X2)))) ) )
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

% (9275)Time limit reached!
% (9275)------------------------------
% (9275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9275)Termination reason: Time limit
% (9275)Termination phase: Saturation

% (9275)Memory used [KB]: 12920
% (9275)Time elapsed: 0.400 s
% (9275)------------------------------
% (9275)------------------------------
fof(f65,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( k2_waybel_0(sK0,sK1,X4) != X3
                  | ~ r1_orders_2(sK1,X2,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
              | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,X2)))) )
            & ( ? [X5] :
                  ( k2_waybel_0(sK0,sK1,X5) = X3
                  & r1_orders_2(sK1,X2,X5)
                  & m1_subset_1(X5,u1_struct_0(sK1)) )
              | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,X2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,X2)))) ) )
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( k2_waybel_0(sK0,sK1,X4) != X3
                | ~ r1_orders_2(sK1,sK2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
            | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) )
          & ( ? [X5] :
                ( k2_waybel_0(sK0,sK1,X5) = X3
                & r1_orders_2(sK1,sK2,X5)
                & m1_subset_1(X5,u1_struct_0(sK1)) )
            | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( k2_waybel_0(sK0,sK1,X4) != X3
              | ~ r1_orders_2(sK1,sK2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
          | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) )
        & ( ? [X5] :
              ( k2_waybel_0(sK0,sK1,X5) = X3
              & r1_orders_2(sK1,sK2,X5)
              & m1_subset_1(X5,u1_struct_0(sK1)) )
          | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ) )
   => ( ( ! [X4] :
            ( k2_waybel_0(sK0,sK1,X4) != sK3
            | ~ r1_orders_2(sK1,sK2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
        | ~ r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) )
      & ( ? [X5] :
            ( k2_waybel_0(sK0,sK1,X5) = sK3
            & r1_orders_2(sK1,sK2,X5)
            & m1_subset_1(X5,u1_struct_0(sK1)) )
        | r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ? [X5] :
        ( k2_waybel_0(sK0,sK1,X5) = sK3
        & r1_orders_2(sK1,sK2,X5)
        & m1_subset_1(X5,u1_struct_0(sK1)) )
   => ( sK3 = k2_waybel_0(sK0,sK1,sK4)
      & r1_orders_2(sK1,sK2,sK4)
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( k2_waybel_0(X0,X1,X4) != X3
                        | ~ r1_orders_2(X1,X2,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) )
                  & ( ? [X5] :
                        ( k2_waybel_0(X0,X1,X5) = X3
                        & r1_orders_2(X1,X2,X5)
                        & m1_subset_1(X5,u1_struct_0(X1)) )
                    | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) ) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( k2_waybel_0(X0,X1,X4) != X3
                        | ~ r1_orders_2(X1,X2,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) )
                  & ( ? [X4] :
                        ( k2_waybel_0(X0,X1,X4) = X3
                        & r1_orders_2(X1,X2,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2)))) ) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2))))
                <~> ? [X4] :
                      ( k2_waybel_0(X0,X1,X4) = X3
                      & r1_orders_2(X1,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2))))
                <~> ? [X4] :
                      ( k2_waybel_0(X0,X1,X4) = X3
                      & r1_orders_2(X1,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ! [X3] :
                    ( r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2))))
                  <=> ? [X4] :
                        ( k2_waybel_0(X0,X1,X4) = X3
                        & r1_orders_2(X1,X2,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(u1_struct_0(k5_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k5_waybel_9(X0,X1,X2))))
                <=> ? [X4] :
                      ( k2_waybel_0(X0,X1,X4) = X3
                      & r1_orders_2(X1,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow19)).

fof(f213,plain,(
    spl11_11 ),
    inference(avatar_split_clause,[],[f84,f210])).

fof(f84,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f208,plain,(
    ~ spl11_10 ),
    inference(avatar_split_clause,[],[f85,f205])).

fof(f85,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

fof(f203,plain,(
    spl11_9 ),
    inference(avatar_split_clause,[],[f86,f200])).

fof(f86,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f68])).

fof(f198,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f87,f195])).

fof(f87,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

fof(f193,plain,(
    spl11_7 ),
    inference(avatar_split_clause,[],[f88,f190])).

fof(f88,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f188,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f89,f185])).

fof(f89,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f68])).

fof(f183,plain,
    ( spl11_1
    | spl11_5 ),
    inference(avatar_split_clause,[],[f90,f180,f162])).

fof(f90,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f68])).

fof(f178,plain,
    ( spl11_1
    | spl11_4 ),
    inference(avatar_split_clause,[],[f91,f175,f162])).

fof(f91,plain,
    ( r1_orders_2(sK1,sK2,sK4)
    | r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f68])).

fof(f173,plain,
    ( spl11_1
    | spl11_3 ),
    inference(avatar_split_clause,[],[f92,f170,f162])).

fof(f92,plain,
    ( sK3 = k2_waybel_0(sK0,sK1,sK4)
    | r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f68])).

fof(f168,plain,
    ( ~ spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f93,f166,f162])).

fof(f93,plain,(
    ! [X4] :
      ( k2_waybel_0(sK0,sK1,X4) != sK3
      | ~ r1_orders_2(sK1,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ r2_hidden(sK3,k2_relset_1(u1_struct_0(k5_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK0),u1_waybel_0(sK0,k5_waybel_9(sK0,sK1,sK2)))) ) ),
    inference(cnf_transformation,[],[f68])).

%------------------------------------------------------------------------------
