%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t4_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:40:59 EDT 2019

% Result     : Theorem 28.71s
% Output     : Refutation 28.71s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 316 expanded)
%              Number of leaves         :   33 ( 139 expanded)
%              Depth                    :   28
%              Number of atoms          :  764 (2444 expanded)
%              Number of equality atoms :   59 ( 253 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3010,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f347,f354,f361,f368,f375,f382,f407,f438,f492,f554,f561,f627,f630,f1309,f1656,f3006])).

fof(f3006,plain,
    ( spl31_45
    | ~ spl31_46
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(avatar_contradiction_clause,[],[f2989])).

fof(f2989,plain,
    ( $false
    | ~ spl31_45
    | ~ spl31_46
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(unit_resulting_resolution,[],[f560,f553,f2988])).

fof(f2988,plain,
    ( ! [X0] :
        ( sP0(sK3,X0)
        | ~ sP0(sK2,X0) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(duplicate_literal_removal,[],[f2986])).

fof(f2986,plain,
    ( ! [X0] :
        ( sP0(sK3,X0)
        | ~ sP0(sK2,X0)
        | sP0(sK3,X0) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(resolution,[],[f2985,f263])).

fof(f263,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X4] :
              ( ~ r1_orders_2(X0,X4,sK10(X0,X1))
              | ~ r1_orders_2(X0,X4,sK9(X0,X1))
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X1)
          & m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
          & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( r1_orders_2(X0,sK11(X0,X1,X5,X6),X6)
                  & r1_orders_2(X0,sK11(X0,X1,X5,X6),X5)
                  & r2_hidden(sK11(X0,X1,X5,X6),X1)
                  & m1_subset_1(sK11(X0,X1,X5,X6),u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f181,f184,f183,f182])).

fof(f182,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  | ~ r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                | ~ r1_orders_2(X0,X4,sK9(X0,X1))
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X3,X1)
            & r2_hidden(sK9(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f183,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_orders_2(X0,X4,X3)
              | ~ r1_orders_2(X0,X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r1_orders_2(X0,X4,sK10(X0,X1))
            | ~ r1_orders_2(X0,X4,X2)
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f184,plain,(
    ! [X6,X5,X1,X0] :
      ( ? [X7] :
          ( r1_orders_2(X0,X7,X6)
          & r1_orders_2(X0,X7,X5)
          & r2_hidden(X7,X1)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,sK11(X0,X1,X5,X6),X6)
        & r1_orders_2(X0,sK11(X0,X1,X5,X6),X5)
        & r2_hidden(sK11(X0,X1,X5,X6),X1)
        & m1_subset_1(sK11(X0,X1,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X4,X3)
                    | ~ r1_orders_2(X0,X4,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ? [X7] :
                    ( r1_orders_2(X0,X7,X6)
                    & r1_orders_2(X0,X7,X5)
                    & r2_hidden(X7,X1)
                    & m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f180])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X4,X3)
                    | ~ r1_orders_2(X0,X4,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( r1_orders_2(X0,X4,X3)
                    & r1_orders_2(X0,X4,X2)
                    & r2_hidden(X4,X1)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,X2)
                  & r2_hidden(X4,X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2985,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(sK3,X0),X0)
        | sP0(sK3,X0)
        | ~ sP0(sK2,X0) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(duplicate_literal_removal,[],[f2983])).

fof(f2983,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(sK3,X0),X0)
        | sP0(sK3,X0)
        | ~ sP0(sK2,X0)
        | sP0(sK3,X0) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(resolution,[],[f2982,f264])).

fof(f264,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f2982,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK10(sK3,X0),X0)
        | ~ r2_hidden(sK9(sK3,X0),X0)
        | sP0(sK3,X0)
        | ~ sP0(sK2,X0) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(duplicate_literal_removal,[],[f2960])).

fof(f2960,plain,
    ( ! [X0] :
        ( sP0(sK3,X0)
        | ~ r2_hidden(sK9(sK3,X0),X0)
        | ~ r2_hidden(sK10(sK3,X0),X0)
        | ~ sP0(sK2,X0)
        | sP0(sK3,X0) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(resolution,[],[f2959,f641])).

fof(f641,plain,
    ( ! [X4] :
        ( m1_subset_1(sK9(sK3,X4),u1_struct_0(sK2))
        | sP0(sK3,X4) )
    | ~ spl31_62 ),
    inference(superposition,[],[f261,f626])).

fof(f626,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ spl31_62 ),
    inference(avatar_component_clause,[],[f625])).

fof(f625,plain,
    ( spl31_62
  <=> u1_struct_0(sK2) = u1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_62])])).

fof(f261,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f2959,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,X0),u1_struct_0(sK2))
        | sP0(sK3,X0)
        | ~ r2_hidden(sK9(sK3,X0),X0)
        | ~ r2_hidden(sK10(sK3,X0),X0)
        | ~ sP0(sK2,X0) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(duplicate_literal_removal,[],[f2937])).

fof(f2937,plain,
    ( ! [X0] :
        ( sP0(sK3,X0)
        | ~ m1_subset_1(sK9(sK3,X0),u1_struct_0(sK2))
        | ~ r2_hidden(sK9(sK3,X0),X0)
        | ~ r2_hidden(sK10(sK3,X0),X0)
        | ~ sP0(sK2,X0)
        | sP0(sK3,X0) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(resolution,[],[f2936,f642])).

fof(f642,plain,
    ( ! [X5] :
        ( m1_subset_1(sK10(sK3,X5),u1_struct_0(sK2))
        | sP0(sK3,X5) )
    | ~ spl31_62 ),
    inference(superposition,[],[f262,f626])).

fof(f262,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f2936,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK10(sK3,X0),u1_struct_0(sK2))
        | sP0(sK3,X0)
        | ~ m1_subset_1(sK9(sK3,X0),u1_struct_0(sK2))
        | ~ r2_hidden(sK9(sK3,X0),X0)
        | ~ r2_hidden(sK10(sK3,X0),X0)
        | ~ sP0(sK2,X0) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(duplicate_literal_removal,[],[f2934])).

fof(f2934,plain,
    ( ! [X0] :
        ( sP0(sK3,X0)
        | ~ m1_subset_1(sK10(sK3,X0),u1_struct_0(sK2))
        | ~ m1_subset_1(sK9(sK3,X0),u1_struct_0(sK2))
        | ~ r2_hidden(sK9(sK3,X0),X0)
        | ~ r2_hidden(sK10(sK3,X0),X0)
        | ~ sP0(sK2,X0)
        | ~ r2_hidden(sK9(sK3,X0),X0)
        | ~ r2_hidden(sK10(sK3,X0),X0)
        | ~ m1_subset_1(sK9(sK3,X0),u1_struct_0(sK2))
        | ~ m1_subset_1(sK10(sK3,X0),u1_struct_0(sK2))
        | ~ sP0(sK2,X0) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(resolution,[],[f2921,f258])).

fof(f258,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(sK11(X0,X1,X5,X6),X1)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f2921,plain,
    ( ! [X19,X18] :
        ( ~ r2_hidden(sK11(sK2,X19,sK10(sK3,X18),sK9(sK3,X18)),X18)
        | sP0(sK3,X18)
        | ~ m1_subset_1(sK10(sK3,X18),u1_struct_0(sK2))
        | ~ m1_subset_1(sK9(sK3,X18),u1_struct_0(sK2))
        | ~ r2_hidden(sK9(sK3,X18),X19)
        | ~ r2_hidden(sK10(sK3,X18),X19)
        | ~ sP0(sK2,X19) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(duplicate_literal_removal,[],[f2920])).

fof(f2920,plain,
    ( ! [X19,X18] :
        ( sP0(sK3,X18)
        | ~ r2_hidden(sK11(sK2,X19,sK10(sK3,X18),sK9(sK3,X18)),X18)
        | ~ m1_subset_1(sK10(sK3,X18),u1_struct_0(sK2))
        | ~ m1_subset_1(sK9(sK3,X18),u1_struct_0(sK2))
        | ~ r2_hidden(sK9(sK3,X18),X19)
        | ~ r2_hidden(sK10(sK3,X18),X19)
        | ~ sP0(sK2,X19)
        | ~ r2_hidden(sK9(sK3,X18),X19)
        | ~ r2_hidden(sK10(sK3,X18),X19)
        | ~ m1_subset_1(sK9(sK3,X18),u1_struct_0(sK2))
        | ~ m1_subset_1(sK10(sK3,X18),u1_struct_0(sK2))
        | ~ sP0(sK2,X19) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(resolution,[],[f2905,f257])).

fof(f257,plain,(
    ! [X6,X0,X5,X1] :
      ( m1_subset_1(sK11(X0,X1,X5,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f2905,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK11(sK2,X4,sK10(sK3,X3),sK9(sK3,X3)),u1_struct_0(sK2))
        | sP0(sK3,X3)
        | ~ r2_hidden(sK11(sK2,X4,sK10(sK3,X3),sK9(sK3,X3)),X3)
        | ~ m1_subset_1(sK10(sK3,X3),u1_struct_0(sK2))
        | ~ m1_subset_1(sK9(sK3,X3),u1_struct_0(sK2))
        | ~ r2_hidden(sK9(sK3,X3),X4)
        | ~ r2_hidden(sK10(sK3,X3),X4)
        | ~ sP0(sK2,X4) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(duplicate_literal_removal,[],[f2904])).

fof(f2904,plain,
    ( ! [X4,X3] :
        ( sP0(sK3,X3)
        | ~ m1_subset_1(sK11(sK2,X4,sK10(sK3,X3),sK9(sK3,X3)),u1_struct_0(sK2))
        | ~ r2_hidden(sK11(sK2,X4,sK10(sK3,X3),sK9(sK3,X3)),X3)
        | ~ m1_subset_1(sK10(sK3,X3),u1_struct_0(sK2))
        | ~ m1_subset_1(sK9(sK3,X3),u1_struct_0(sK2))
        | ~ r2_hidden(sK9(sK3,X3),X4)
        | ~ r2_hidden(sK10(sK3,X3),X4)
        | ~ m1_subset_1(sK9(sK3,X3),u1_struct_0(sK2))
        | ~ sP0(sK2,X4)
        | ~ r2_hidden(sK9(sK3,X3),X4)
        | ~ r2_hidden(sK10(sK3,X3),X4)
        | ~ m1_subset_1(sK9(sK3,X3),u1_struct_0(sK2))
        | ~ m1_subset_1(sK10(sK3,X3),u1_struct_0(sK2))
        | ~ sP0(sK2,X4) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(resolution,[],[f2500,f260])).

fof(f260,plain,(
    ! [X6,X0,X5,X1] :
      ( r1_orders_2(X0,sK11(X0,X1,X5,X6),X6)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f2500,plain,
    ( ! [X6,X7,X5] :
        ( ~ r1_orders_2(sK2,sK11(sK2,X6,sK10(sK3,X5),X7),sK9(sK3,X5))
        | sP0(sK3,X5)
        | ~ m1_subset_1(sK11(sK2,X6,sK10(sK3,X5),X7),u1_struct_0(sK2))
        | ~ r2_hidden(sK11(sK2,X6,sK10(sK3,X5),X7),X5)
        | ~ m1_subset_1(sK10(sK3,X5),u1_struct_0(sK2))
        | ~ m1_subset_1(sK9(sK3,X5),u1_struct_0(sK2))
        | ~ r2_hidden(X7,X6)
        | ~ r2_hidden(sK10(sK3,X5),X6)
        | ~ m1_subset_1(X7,u1_struct_0(sK2))
        | ~ sP0(sK2,X6) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(duplicate_literal_removal,[],[f2499])).

fof(f2499,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(sK10(sK3,X5),u1_struct_0(sK2))
        | sP0(sK3,X5)
        | ~ m1_subset_1(sK11(sK2,X6,sK10(sK3,X5),X7),u1_struct_0(sK2))
        | ~ r2_hidden(sK11(sK2,X6,sK10(sK3,X5),X7),X5)
        | ~ r1_orders_2(sK2,sK11(sK2,X6,sK10(sK3,X5),X7),sK9(sK3,X5))
        | ~ m1_subset_1(sK9(sK3,X5),u1_struct_0(sK2))
        | ~ r2_hidden(X7,X6)
        | ~ r2_hidden(sK10(sK3,X5),X6)
        | ~ m1_subset_1(X7,u1_struct_0(sK2))
        | ~ m1_subset_1(sK10(sK3,X5),u1_struct_0(sK2))
        | ~ sP0(sK2,X6) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(resolution,[],[f2175,f259])).

fof(f259,plain,(
    ! [X6,X0,X5,X1] :
      ( r1_orders_2(X0,sK11(X0,X1,X5,X6),X5)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f2175,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK2,X0,sK10(sK3,X1))
        | ~ m1_subset_1(sK10(sK3,X1),u1_struct_0(sK2))
        | sP0(sK3,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r2_hidden(X0,X1)
        | ~ r1_orders_2(sK2,X0,sK9(sK3,X1))
        | ~ m1_subset_1(sK9(sK3,X1),u1_struct_0(sK2)) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(duplicate_literal_removal,[],[f2172])).

fof(f2172,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK2,X0,sK10(sK3,X1))
        | ~ m1_subset_1(sK10(sK3,X1),u1_struct_0(sK2))
        | sP0(sK3,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r2_hidden(X0,X1)
        | ~ r1_orders_2(sK2,X0,sK9(sK3,X1))
        | ~ m1_subset_1(sK9(sK3,X1),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(resolution,[],[f1659,f1655])).

fof(f1655,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK3,X0,X1)
        | ~ r1_orders_2(sK2,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl31_260 ),
    inference(avatar_component_clause,[],[f1654])).

fof(f1654,plain,
    ( spl31_260
  <=> ! [X1,X0] :
        ( r1_orders_2(sK3,X0,X1)
        | ~ r1_orders_2(sK2,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_260])])).

fof(f1659,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK3,X0,sK9(sK3,X1))
        | ~ r1_orders_2(sK2,X0,sK10(sK3,X1))
        | ~ m1_subset_1(sK10(sK3,X1),u1_struct_0(sK2))
        | sP0(sK3,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(duplicate_literal_removal,[],[f1658])).

fof(f1658,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_orders_2(sK2,X0,sK10(sK3,X1))
        | ~ m1_subset_1(sK10(sK3,X1),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | sP0(sK3,X1)
        | ~ r1_orders_2(sK3,X0,sK9(sK3,X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl31_62
    | ~ spl31_260 ),
    inference(forward_demodulation,[],[f1657,f626])).

fof(f1657,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK2,X0,sK10(sK3,X1))
        | ~ m1_subset_1(sK10(sK3,X1),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | sP0(sK3,X1)
        | ~ r1_orders_2(sK3,X0,sK9(sK3,X1))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl31_260 ),
    inference(resolution,[],[f1655,f265])).

fof(f265,plain,(
    ! [X4,X0,X1] :
      ( ~ r1_orders_2(X0,X4,sK10(X0,X1))
      | sP0(X0,X1)
      | ~ r1_orders_2(X0,X4,sK9(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f553,plain,
    ( ~ sP0(sK3,sK5)
    | ~ spl31_45 ),
    inference(avatar_component_clause,[],[f552])).

fof(f552,plain,
    ( spl31_45
  <=> ~ sP0(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_45])])).

fof(f560,plain,
    ( sP0(sK2,sK5)
    | ~ spl31_46 ),
    inference(avatar_component_clause,[],[f559])).

fof(f559,plain,
    ( spl31_46
  <=> sP0(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_46])])).

fof(f1656,plain,
    ( spl31_260
    | ~ spl31_1
    | ~ spl31_188 ),
    inference(avatar_split_clause,[],[f1336,f1307,f342,f1654])).

fof(f342,plain,
    ( spl31_1
  <=> ~ l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1])])).

fof(f1307,plain,
    ( spl31_188
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ l1_orders_2(X0)
        | r1_orders_2(sK3,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_orders_2(X0,X1,X2)
        | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_188])])).

fof(f1336,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK2)
        | r1_orders_2(sK3,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_orders_2(sK2,X0,X1) )
    | ~ spl31_188 ),
    inference(duplicate_literal_removal,[],[f1335])).

fof(f1335,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK2)
        | r1_orders_2(sK3,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_orders_2(sK2,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2)) )
    | ~ spl31_188 ),
    inference(equality_resolution,[],[f1308])).

fof(f1308,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | r1_orders_2(sK3,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
    | ~ spl31_188 ),
    inference(avatar_component_clause,[],[f1307])).

fof(f1309,plain,
    ( ~ spl31_3
    | spl31_188
    | ~ spl31_20
    | ~ spl31_62 ),
    inference(avatar_split_clause,[],[f1128,f625,f436,f1307,f349])).

fof(f349,plain,
    ( spl31_3
  <=> ~ l1_orders_2(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_3])])).

fof(f436,plain,
    ( spl31_20
  <=> g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_20])])).

fof(f1128,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_orders_2(sK3,X1,X2)
        | ~ l1_orders_2(sK3)
        | ~ l1_orders_2(X0) )
    | ~ spl31_20
    | ~ spl31_62 ),
    inference(forward_demodulation,[],[f1127,f626])).

fof(f1127,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK2))
        | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_orders_2(sK3,X1,X2)
        | ~ l1_orders_2(sK3)
        | ~ l1_orders_2(X0) )
    | ~ spl31_20
    | ~ spl31_62 ),
    inference(forward_demodulation,[],[f468,f626])).

fof(f468,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_orders_2(sK3,X1,X2)
        | ~ l1_orders_2(sK3)
        | ~ l1_orders_2(X0) )
    | ~ spl31_20 ),
    inference(superposition,[],[f336,f437])).

fof(f437,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | ~ spl31_20 ),
    inference(avatar_component_clause,[],[f436])).

fof(f336,plain,(
    ! [X4,X0,X5,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X1,X4,X5)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f335])).

fof(f335,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f252])).

fof(f252,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f113])).

fof(f113,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f70])).

fof(f70,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => ( ( r2_orders_2(X0,X2,X3)
                                 => r2_orders_2(X1,X4,X5) )
                                & ( r1_orders_2(X0,X2,X3)
                                 => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t4_waybel_0.p',t1_yellow_0)).

fof(f630,plain,
    ( ~ spl31_0
    | spl31_61 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | ~ spl31_0
    | ~ spl31_61 ),
    inference(unit_resulting_resolution,[],[f346,f620,f250])).

fof(f250,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t4_waybel_0.p',dt_u1_orders_2)).

fof(f620,plain,
    ( ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ spl31_61 ),
    inference(avatar_component_clause,[],[f619])).

fof(f619,plain,
    ( spl31_61
  <=> ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_61])])).

fof(f346,plain,
    ( l1_orders_2(sK2)
    | ~ spl31_0 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl31_0
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_0])])).

fof(f627,plain,
    ( ~ spl31_61
    | spl31_62
    | ~ spl31_20 ),
    inference(avatar_split_clause,[],[f614,f436,f625,f619])).

fof(f614,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ spl31_20 ),
    inference(equality_resolution,[],[f473])).

fof(f473,plain,
    ( ! [X12,X13] :
        ( g1_orders_2(X12,X13) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
        | u1_struct_0(sK3) = X12
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X12))) )
    | ~ spl31_20 ),
    inference(superposition,[],[f299,f437])).

fof(f299,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t4_waybel_0.p',free_g1_orders_2)).

fof(f561,plain,
    ( spl31_46
    | ~ spl31_7
    | ~ spl31_30 ),
    inference(avatar_split_clause,[],[f493,f490,f363,f559])).

fof(f363,plain,
    ( spl31_7
  <=> ~ v2_waybel_0(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_7])])).

fof(f490,plain,
    ( spl31_30
  <=> sP1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_30])])).

fof(f493,plain,
    ( ~ v2_waybel_0(sK5,sK2)
    | sP0(sK2,sK5)
    | ~ spl31_30 ),
    inference(resolution,[],[f491,f255])).

fof(f255,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v2_waybel_0(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ( ( v2_waybel_0(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_waybel_0(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f178])).

fof(f178,plain,(
    ! [X1,X0] :
      ( ( ( v2_waybel_0(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v2_waybel_0(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f165])).

fof(f165,plain,(
    ! [X1,X0] :
      ( ( v2_waybel_0(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f491,plain,
    ( sP1(sK5,sK2)
    | ~ spl31_30 ),
    inference(avatar_component_clause,[],[f490])).

fof(f554,plain,
    ( spl31_4
    | ~ spl31_45
    | ~ spl31_12 ),
    inference(avatar_split_clause,[],[f409,f405,f552,f356])).

fof(f356,plain,
    ( spl31_4
  <=> v2_waybel_0(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_4])])).

fof(f405,plain,
    ( spl31_12
  <=> sP1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_12])])).

fof(f409,plain,
    ( ~ sP0(sK3,sK5)
    | v2_waybel_0(sK5,sK3)
    | ~ spl31_12 ),
    inference(resolution,[],[f406,f256])).

fof(f256,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v2_waybel_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f179])).

fof(f406,plain,
    ( sP1(sK5,sK3)
    | ~ spl31_12 ),
    inference(avatar_component_clause,[],[f405])).

fof(f492,plain,
    ( ~ spl31_1
    | spl31_30
    | ~ spl31_10 ),
    inference(avatar_split_clause,[],[f392,f380,f490,f342])).

fof(f380,plain,
    ( spl31_10
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_10])])).

fof(f392,plain,
    ( sP1(sK5,sK2)
    | ~ l1_orders_2(sK2)
    | ~ spl31_10 ),
    inference(resolution,[],[f381,f266])).

fof(f266,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f166])).

fof(f166,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f118,f165,f164])).

fof(f118,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X4,X3)
                                & r1_orders_2(X0,X4,X2)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t4_waybel_0.p',d2_waybel_0)).

fof(f381,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl31_10 ),
    inference(avatar_component_clause,[],[f380])).

fof(f438,plain,(
    spl31_20 ),
    inference(avatar_split_clause,[],[f222,f436])).

fof(f222,plain,(
    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f171])).

fof(f171,plain,
    ( ~ v2_waybel_0(sK5,sK3)
    & v2_waybel_0(sK4,sK2)
    & sK4 = sK5
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    & l1_orders_2(sK3)
    & l1_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f89,f170,f169,f168,f167])).

fof(f167,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_waybel_0(X3,X1)
                    & v2_waybel_0(X2,X0)
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_waybel_0(X3,X1)
                  & v2_waybel_0(X2,sK2)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f168,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_waybel_0(X3,X1)
                  & v2_waybel_0(X2,X0)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_waybel_0(X3,sK3)
                & v2_waybel_0(X2,X0)
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_waybel_0(X3,X1)
              & v2_waybel_0(X2,X0)
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ~ v2_waybel_0(X3,X1)
            & v2_waybel_0(sK4,X0)
            & sK4 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ v2_waybel_0(X3,X1)
          & v2_waybel_0(X2,X0)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_waybel_0(sK5,X1)
        & v2_waybel_0(X2,X0)
        & sK5 = X2
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_waybel_0(X3,X1)
                  & v2_waybel_0(X2,X0)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_waybel_0(X3,X1)
                  & v2_waybel_0(X2,X0)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( ( v2_waybel_0(X2,X0)
                          & X2 = X3 )
                       => v2_waybel_0(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_waybel_0(X2,X0)
                        & X2 = X3 )
                     => v2_waybel_0(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t4_waybel_0.p',t4_waybel_0)).

fof(f407,plain,
    ( ~ spl31_3
    | spl31_12
    | ~ spl31_8 ),
    inference(avatar_split_clause,[],[f383,f373,f405,f349])).

fof(f373,plain,
    ( spl31_8
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_8])])).

fof(f383,plain,
    ( sP1(sK5,sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl31_8 ),
    inference(resolution,[],[f374,f266])).

fof(f374,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl31_8 ),
    inference(avatar_component_clause,[],[f373])).

fof(f382,plain,(
    spl31_10 ),
    inference(avatar_split_clause,[],[f330,f380])).

fof(f330,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(definition_unfolding,[],[f223,f225])).

fof(f225,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f171])).

fof(f223,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f171])).

fof(f375,plain,(
    spl31_8 ),
    inference(avatar_split_clause,[],[f224,f373])).

fof(f224,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f171])).

fof(f368,plain,(
    spl31_6 ),
    inference(avatar_split_clause,[],[f329,f366])).

fof(f366,plain,
    ( spl31_6
  <=> v2_waybel_0(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_6])])).

fof(f329,plain,(
    v2_waybel_0(sK5,sK2) ),
    inference(definition_unfolding,[],[f226,f225])).

fof(f226,plain,(
    v2_waybel_0(sK4,sK2) ),
    inference(cnf_transformation,[],[f171])).

fof(f361,plain,(
    ~ spl31_5 ),
    inference(avatar_split_clause,[],[f227,f359])).

fof(f359,plain,
    ( spl31_5
  <=> ~ v2_waybel_0(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_5])])).

fof(f227,plain,(
    ~ v2_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f171])).

fof(f354,plain,(
    spl31_2 ),
    inference(avatar_split_clause,[],[f221,f352])).

fof(f352,plain,
    ( spl31_2
  <=> l1_orders_2(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_2])])).

fof(f221,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f171])).

fof(f347,plain,(
    spl31_0 ),
    inference(avatar_split_clause,[],[f220,f345])).

fof(f220,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f171])).
%------------------------------------------------------------------------------
