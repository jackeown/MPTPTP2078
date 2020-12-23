%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1996+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:02 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  314 (2627 expanded)
%              Number of leaves         :   46 ( 951 expanded)
%              Depth                    :   30
%              Number of atoms          : 2084 (38688 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1362,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f134,f138,f142,f146,f150,f154,f158,f163,f424,f446,f474,f642,f726,f751,f1179,f1225,f1321,f1347,f1356])).

fof(f1356,plain,
    ( ~ spl15_15
    | ~ spl15_38
    | ~ spl15_3
    | ~ spl15_5
    | ~ spl15_7
    | spl15_28 ),
    inference(avatar_split_clause,[],[f1355,f910,f152,f144,f136,f1129,f592])).

fof(f592,plain,
    ( spl15_15
  <=> m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).

fof(f1129,plain,
    ( spl15_38
  <=> r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_38])])).

fof(f136,plain,
    ( spl15_3
  <=> r2_hidden(k7_yellow_3(sK0,sK0,sK3,sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).

fof(f144,plain,
    ( spl15_5
  <=> m1_subset_1(sK5,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).

fof(f152,plain,
    ( spl15_7
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).

fof(f910,plain,
    ( spl15_28
  <=> r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_28])])).

fof(f1355,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK3)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl15_3
    | ~ spl15_5
    | ~ spl15_7
    | spl15_28 ),
    inference(subsumption_resolution,[],[f1354,f528])).

fof(f528,plain,
    ( r1_orders_2(sK0,sK5,sK5)
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f527,f165])).

fof(f165,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f164,f80])).

fof(f80,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ( ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k12_lattice3(sK0,sK4,sK5)),sK1)
        & r2_hidden(k7_yellow_3(sK0,sK0,sK3,sK5),sK1)
        & r2_hidden(k7_yellow_3(sK0,sK0,sK2,sK4),sK1)
        & m1_subset_1(sK5,u1_struct_0(sK0))
        & m1_subset_1(sK4,u1_struct_0(sK0))
        & m1_subset_1(sK3,u1_struct_0(sK0))
        & m1_subset_1(sK2,u1_struct_0(sK0)) )
      | ~ v5_waybel_7(sK1,sK0) )
    & ( ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X6,X7),k12_lattice3(sK0,X8,X9)),sK1)
                      | ~ r2_hidden(k7_yellow_3(sK0,sK0,X7,X9),sK1)
                      | ~ r2_hidden(k7_yellow_3(sK0,sK0,X6,X8),sK1)
                      | ~ m1_subset_1(X9,u1_struct_0(sK0)) )
                  | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
              | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
          | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
      | v5_waybel_7(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    & v5_waybel_4(sK1,sK0)
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f47,f53,f52,f51,f50,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ? [X4] :
                          ( ? [X5] :
                              ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                              & r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                              & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                              & m1_subset_1(X5,u1_struct_0(X0)) )
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v5_waybel_7(X1,X0) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ! [X8] :
                          ( ! [X9] :
                              ( r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X6,X7),k12_lattice3(X0,X8,X9)),X1)
                              | ~ r2_hidden(k7_yellow_3(X0,X0,X7,X9),X1)
                              | ~ r2_hidden(k7_yellow_3(X0,X0,X6,X8),X1)
                              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                          | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | v5_waybel_7(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
            & v5_waybel_4(X1,X0) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X2,X3),k12_lattice3(sK0,X4,X5)),X1)
                            & r2_hidden(k7_yellow_3(sK0,sK0,X3,X5),X1)
                            & r2_hidden(k7_yellow_3(sK0,sK0,X2,X4),X1)
                            & m1_subset_1(X5,u1_struct_0(sK0)) )
                        & m1_subset_1(X4,u1_struct_0(sK0)) )
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ v5_waybel_7(X1,sK0) )
          & ( ! [X6] :
                ( ! [X7] :
                    ( ! [X8] :
                        ( ! [X9] :
                            ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X6,X7),k12_lattice3(sK0,X8,X9)),X1)
                            | ~ r2_hidden(k7_yellow_3(sK0,sK0,X7,X9),X1)
                            | ~ r2_hidden(k7_yellow_3(sK0,sK0,X6,X8),X1)
                            | ~ m1_subset_1(X9,u1_struct_0(sK0)) )
                        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
                    | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
                | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
            | v5_waybel_7(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
          & v5_waybel_4(X1,sK0) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X2,X3),k12_lattice3(sK0,X4,X5)),X1)
                          & r2_hidden(k7_yellow_3(sK0,sK0,X3,X5),X1)
                          & r2_hidden(k7_yellow_3(sK0,sK0,X2,X4),X1)
                          & m1_subset_1(X5,u1_struct_0(sK0)) )
                      & m1_subset_1(X4,u1_struct_0(sK0)) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          | ~ v5_waybel_7(X1,sK0) )
        & ( ! [X6] :
              ( ! [X7] :
                  ( ! [X8] :
                      ( ! [X9] :
                          ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X6,X7),k12_lattice3(sK0,X8,X9)),X1)
                          | ~ r2_hidden(k7_yellow_3(sK0,sK0,X7,X9),X1)
                          | ~ r2_hidden(k7_yellow_3(sK0,sK0,X6,X8),X1)
                          | ~ m1_subset_1(X9,u1_struct_0(sK0)) )
                      | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
                  | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
              | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
          | v5_waybel_7(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        & v5_waybel_4(X1,sK0) )
   => ( ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X2,X3),k12_lattice3(sK0,X4,X5)),sK1)
                        & r2_hidden(k7_yellow_3(sK0,sK0,X3,X5),sK1)
                        & r2_hidden(k7_yellow_3(sK0,sK0,X2,X4),sK1)
                        & m1_subset_1(X5,u1_struct_0(sK0)) )
                    & m1_subset_1(X4,u1_struct_0(sK0)) )
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        | ~ v5_waybel_7(sK1,sK0) )
      & ( ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X6,X7),k12_lattice3(sK0,X8,X9)),sK1)
                        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X7,X9),sK1)
                        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X6,X8),sK1)
                        | ~ m1_subset_1(X9,u1_struct_0(sK0)) )
                    | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
                | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
            | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
        | v5_waybel_7(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      & v5_waybel_4(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X2,X3),k12_lattice3(sK0,X4,X5)),sK1)
                    & r2_hidden(k7_yellow_3(sK0,sK0,X3,X5),sK1)
                    & r2_hidden(k7_yellow_3(sK0,sK0,X2,X4),sK1)
                    & m1_subset_1(X5,u1_struct_0(sK0)) )
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,X3),k12_lattice3(sK0,X4,X5)),sK1)
                  & r2_hidden(k7_yellow_3(sK0,sK0,X3,X5),sK1)
                  & r2_hidden(k7_yellow_3(sK0,sK0,sK2,X4),sK1)
                  & m1_subset_1(X5,u1_struct_0(sK0)) )
              & m1_subset_1(X4,u1_struct_0(sK0)) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,X3),k12_lattice3(sK0,X4,X5)),sK1)
                & r2_hidden(k7_yellow_3(sK0,sK0,X3,X5),sK1)
                & r2_hidden(k7_yellow_3(sK0,sK0,sK2,X4),sK1)
                & m1_subset_1(X5,u1_struct_0(sK0)) )
            & m1_subset_1(X4,u1_struct_0(sK0)) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k12_lattice3(sK0,X4,X5)),sK1)
              & r2_hidden(k7_yellow_3(sK0,sK0,sK3,X5),sK1)
              & r2_hidden(k7_yellow_3(sK0,sK0,sK2,X4),sK1)
              & m1_subset_1(X5,u1_struct_0(sK0)) )
          & m1_subset_1(X4,u1_struct_0(sK0)) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k12_lattice3(sK0,X4,X5)),sK1)
            & r2_hidden(k7_yellow_3(sK0,sK0,sK3,X5),sK1)
            & r2_hidden(k7_yellow_3(sK0,sK0,sK2,X4),sK1)
            & m1_subset_1(X5,u1_struct_0(sK0)) )
        & m1_subset_1(X4,u1_struct_0(sK0)) )
   => ( ? [X5] :
          ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k12_lattice3(sK0,sK4,X5)),sK1)
          & r2_hidden(k7_yellow_3(sK0,sK0,sK3,X5),sK1)
          & r2_hidden(k7_yellow_3(sK0,sK0,sK2,sK4),sK1)
          & m1_subset_1(X5,u1_struct_0(sK0)) )
      & m1_subset_1(sK4,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X5] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k12_lattice3(sK0,sK4,X5)),sK1)
        & r2_hidden(k7_yellow_3(sK0,sK0,sK3,X5),sK1)
        & r2_hidden(k7_yellow_3(sK0,sK0,sK2,sK4),sK1)
        & m1_subset_1(X5,u1_struct_0(sK0)) )
   => ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k12_lattice3(sK0,sK4,sK5)),sK1)
      & r2_hidden(k7_yellow_3(sK0,sK0,sK3,sK5),sK1)
      & r2_hidden(k7_yellow_3(sK0,sK0,sK2,sK4),sK1)
      & m1_subset_1(sK5,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v5_waybel_7(X1,X0) )
          & ( ! [X6] :
                ( ! [X7] :
                    ( ! [X8] :
                        ( ! [X9] :
                            ( r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X6,X7),k12_lattice3(X0,X8,X9)),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X7,X9),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X6,X8),X1)
                            | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                        | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | v5_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v5_waybel_7(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v5_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v5_waybel_7(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v5_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_waybel_7(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_waybel_7(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              & v5_waybel_4(X1,X0) )
           => ( v5_waybel_7(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ( ( r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                                  & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1) )
                               => r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1) ) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              & v5_waybel_4(X1,X0) )
           => ( v5_waybel_7(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ( ( r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                                  & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1) )
                               => r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1) ) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              & v5_waybel_4(X1,X0) )
           => ( v5_waybel_7(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ( ( r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                                  & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1) )
                               => r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1) ) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              & v5_waybel_4(X1,X0) )
           => ( v5_waybel_7(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ( ( r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                                  & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1) )
                               => r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
            & v5_waybel_4(X1,X0) )
         => ( v5_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                                & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1) )
                             => r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_waybel_7)).

fof(f164,plain,
    ( ~ v2_struct_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f91,f79])).

fof(f79,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f527,plain,
    ( r1_orders_2(sK0,sK5,sK5)
    | v2_struct_0(sK0)
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f526,f77])).

fof(f77,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f526,plain,
    ( r1_orders_2(sK0,sK5,sK5)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f525,f80])).

fof(f525,plain,
    ( r1_orders_2(sK0,sK5,sK5)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f524,f145])).

fof(f145,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ spl15_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f524,plain,
    ( r1_orders_2(sK0,sK5,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_5 ),
    inference(duplicate_literal_removal,[],[f523])).

fof(f523,plain,
    ( r1_orders_2(sK0,sK5,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_5 ),
    inference(resolution,[],[f507,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f507,plain,
    ( r3_orders_2(sK0,sK5,sK5)
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f506,f165])).

fof(f506,plain,
    ( r3_orders_2(sK0,sK5,sK5)
    | v2_struct_0(sK0)
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f505,f77])).

fof(f505,plain,
    ( r3_orders_2(sK0,sK5,sK5)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f503,f80])).

fof(f503,plain,
    ( r3_orders_2(sK0,sK5,sK5)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_5 ),
    inference(resolution,[],[f145,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f119,f118])).

fof(f118,plain,(
    ! [X0] : m1_subset_1(sK14(X0),X0) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(sK14(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f6,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK14(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f1354,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK3)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK5,sK5)
    | ~ spl15_3
    | ~ spl15_5
    | ~ spl15_7
    | spl15_28 ),
    inference(subsumption_resolution,[],[f1349,f145])).

fof(f1349,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK3)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK5,sK5)
    | ~ spl15_3
    | ~ spl15_5
    | ~ spl15_7
    | spl15_28 ),
    inference(resolution,[],[f911,f623])).

fof(f623,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X1,X0),sK1)
        | ~ r1_orders_2(sK0,X1,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5,X0) )
    | ~ spl15_3
    | ~ spl15_5
    | ~ spl15_7 ),
    inference(subsumption_resolution,[],[f622,f153])).

fof(f153,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl15_7 ),
    inference(avatar_component_clause,[],[f152])).

fof(f622,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK5,X0)
        | ~ r1_orders_2(sK0,X1,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X1,X0),sK1) )
    | ~ spl15_3
    | ~ spl15_5
    | ~ spl15_7 ),
    inference(subsumption_resolution,[],[f621,f145])).

fof(f621,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK5,X0)
        | ~ r1_orders_2(sK0,X1,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X1,X0),sK1) )
    | ~ spl15_3
    | ~ spl15_5
    | ~ spl15_7 ),
    inference(resolution,[],[f534,f340])).

fof(f340,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X0),sK1)
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ r1_orders_2(sK0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(X3,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f339,f80])).

fof(f339,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ r2_hidden(k4_tarski(X2,X0),sK1)
      | ~ r1_orders_2(sK0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(X3,X1),sK1)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f337,f170])).

fof(f170,plain,(
    v2_waybel_4(sK1,sK0) ),
    inference(subsumption_resolution,[],[f169,f165])).

fof(f169,plain,
    ( v2_waybel_4(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f168,f80])).

fof(f168,plain,
    ( v2_waybel_4(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f166,f81])).

fof(f81,plain,(
    v5_waybel_4(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f166,plain,
    ( ~ v5_waybel_4(sK1,sK0)
    | v2_waybel_4(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f101,f82])).

fof(f82,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v5_waybel_4(X1,X0)
      | v2_waybel_4(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_waybel_4(X1,X0)
          | ~ v5_waybel_4(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_waybel_4(X1,X0)
          | ~ v5_waybel_4(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
         => ( v5_waybel_4(X1,X0)
           => v2_waybel_4(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
         => ( v5_waybel_4(X1,X0)
           => ( v2_waybel_4(X1,X0)
              & v1_waybel_4(X1,X0) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
         => ( v5_waybel_4(X1,X0)
           => ( v3_waybel_4(X1,X0)
              & v2_waybel_4(X1,X0)
              & v1_waybel_4(X1,X0) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
         => ( v5_waybel_4(X1,X0)
           => ( v4_waybel_4(X1,X0)
              & v3_waybel_4(X1,X0)
              & v2_waybel_4(X1,X0)
              & v1_waybel_4(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_waybel_4)).

fof(f337,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ r2_hidden(k4_tarski(X2,X0),sK1)
      | ~ r1_orders_2(sK0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v2_waybel_4(sK1,sK0)
      | r2_hidden(k4_tarski(X3,X1),sK1)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f92,f82])).

fof(f92,plain,(
    ! [X6,X0,X8,X7,X1,X9] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ r1_orders_2(X0,X7,X8)
      | ~ r2_hidden(k4_tarski(X6,X7),X1)
      | ~ r1_orders_2(X0,X9,X6)
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v2_waybel_4(X1,X0)
      | r2_hidden(k4_tarski(X9,X8),X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_4(X1,X0)
              | ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X1)
                & r1_orders_2(X0,sK7(X0,X1),sK8(X0,X1))
                & r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
                & r1_orders_2(X0,sK9(X0,X1),sK6(X0,X1))
                & m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ! [X8] :
                          ( ! [X9] :
                              ( r2_hidden(k4_tarski(X9,X8),X1)
                              | ~ r1_orders_2(X0,X7,X8)
                              | ~ r2_hidden(k4_tarski(X6,X7),X1)
                              | ~ r1_orders_2(X0,X9,X6)
                              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                          | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ v2_waybel_4(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f56,f60,f59,f58,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                      & r1_orders_2(X0,X3,X4)
                      & r2_hidden(k4_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X5,X2)
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                    & r1_orders_2(X0,X3,X4)
                    & r2_hidden(k4_tarski(sK6(X0,X1),X3),X1)
                    & r1_orders_2(X0,X5,sK6(X0,X1))
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                  & r1_orders_2(X0,X3,X4)
                  & r2_hidden(k4_tarski(sK6(X0,X1),X3),X1)
                  & r1_orders_2(X0,X5,sK6(X0,X1))
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                & r1_orders_2(X0,sK7(X0,X1),X4)
                & r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
                & r1_orders_2(X0,X5,sK6(X0,X1))
                & m1_subset_1(X5,u1_struct_0(X0)) )
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_hidden(k4_tarski(X5,X4),X1)
              & r1_orders_2(X0,sK7(X0,X1),X4)
              & r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
              & r1_orders_2(X0,X5,sK6(X0,X1))
              & m1_subset_1(X5,u1_struct_0(X0)) )
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ? [X5] :
            ( ~ r2_hidden(k4_tarski(X5,sK8(X0,X1)),X1)
            & r1_orders_2(X0,sK7(X0,X1),sK8(X0,X1))
            & r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
            & r1_orders_2(X0,X5,sK6(X0,X1))
            & m1_subset_1(X5,u1_struct_0(X0)) )
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X5] :
          ( ~ r2_hidden(k4_tarski(X5,sK8(X0,X1)),X1)
          & r1_orders_2(X0,sK7(X0,X1),sK8(X0,X1))
          & r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
          & r1_orders_2(X0,X5,sK6(X0,X1))
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X1)
        & r1_orders_2(X0,sK7(X0,X1),sK8(X0,X1))
        & r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
        & r1_orders_2(X0,sK9(X0,X1),sK6(X0,X1))
        & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_4(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ? [X4] :
                          ( ? [X5] :
                              ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                              & r1_orders_2(X0,X3,X4)
                              & r2_hidden(k4_tarski(X2,X3),X1)
                              & r1_orders_2(X0,X5,X2)
                              & m1_subset_1(X5,u1_struct_0(X0)) )
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ! [X8] :
                          ( ! [X9] :
                              ( r2_hidden(k4_tarski(X9,X8),X1)
                              | ~ r1_orders_2(X0,X7,X8)
                              | ~ r2_hidden(k4_tarski(X6,X7),X1)
                              | ~ r1_orders_2(X0,X9,X6)
                              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                          | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ v2_waybel_4(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_4(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ? [X4] :
                          ( ? [X5] :
                              ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                              & r1_orders_2(X0,X3,X4)
                              & r2_hidden(k4_tarski(X2,X3),X1)
                              & r1_orders_2(X0,X5,X2)
                              & m1_subset_1(X5,u1_struct_0(X0)) )
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( r2_hidden(k4_tarski(X5,X4),X1)
                              | ~ r1_orders_2(X0,X3,X4)
                              | ~ r2_hidden(k4_tarski(X2,X3),X1)
                              | ~ r1_orders_2(X0,X5,X2)
                              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_4(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_4(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r1_orders_2(X0,X3,X4)
                            | ~ r2_hidden(k4_tarski(X2,X3),X1)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_4(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r1_orders_2(X0,X3,X4)
                            | ~ r2_hidden(k4_tarski(X2,X3),X1)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
         => ( v2_waybel_4(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X3,X4)
                                & r2_hidden(k4_tarski(X2,X3),X1)
                                & r1_orders_2(X0,X5,X2) )
                             => r2_hidden(k4_tarski(X5,X4),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_waybel_4)).

fof(f534,plain,
    ( r2_hidden(k4_tarski(sK3,sK5),sK1)
    | ~ spl15_3
    | ~ spl15_5
    | ~ spl15_7 ),
    inference(subsumption_resolution,[],[f533,f165])).

fof(f533,plain,
    ( r2_hidden(k4_tarski(sK3,sK5),sK1)
    | v2_struct_0(sK0)
    | ~ spl15_3
    | ~ spl15_5
    | ~ spl15_7 ),
    inference(subsumption_resolution,[],[f532,f80])).

fof(f532,plain,
    ( r2_hidden(k4_tarski(sK3,sK5),sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_3
    | ~ spl15_5
    | ~ spl15_7 ),
    inference(subsumption_resolution,[],[f531,f153])).

fof(f531,plain,
    ( r2_hidden(k4_tarski(sK3,sK5),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_3
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f530,f145])).

fof(f530,plain,
    ( r2_hidden(k4_tarski(sK3,sK5),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_3 ),
    inference(duplicate_literal_removal,[],[f529])).

fof(f529,plain,
    ( r2_hidden(k4_tarski(sK3,sK5),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_3 ),
    inference(superposition,[],[f137,f124])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X2,X3) = k7_yellow_3(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X2,X3) = k7_yellow_3(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X2,X3) = k7_yellow_3(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X1))
        & m1_subset_1(X2,u1_struct_0(X0))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k4_tarski(X2,X3) = k7_yellow_3(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_yellow_3)).

fof(f137,plain,
    ( r2_hidden(k7_yellow_3(sK0,sK0,sK3,sK5),sK1)
    | ~ spl15_3 ),
    inference(avatar_component_clause,[],[f136])).

fof(f911,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | spl15_28 ),
    inference(avatar_component_clause,[],[f910])).

fof(f1347,plain,
    ( ~ spl15_15
    | ~ spl15_28
    | ~ spl15_5
    | spl15_23 ),
    inference(avatar_split_clause,[],[f1346,f724,f144,f910,f592])).

fof(f724,plain,
    ( spl15_23
  <=> r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_23])])).

fof(f1346,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl15_5
    | spl15_23 ),
    inference(subsumption_resolution,[],[f1345,f165])).

fof(f1345,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl15_5
    | spl15_23 ),
    inference(subsumption_resolution,[],[f1344,f80])).

fof(f1344,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_5
    | spl15_23 ),
    inference(subsumption_resolution,[],[f1343,f145])).

fof(f1343,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_23 ),
    inference(duplicate_literal_removal,[],[f1342])).

fof(f1342,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_23 ),
    inference(superposition,[],[f725,f124])).

fof(f725,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | spl15_23 ),
    inference(avatar_component_clause,[],[f724])).

fof(f1321,plain,
    ( ~ spl15_7
    | ~ spl15_8
    | spl15_43 ),
    inference(avatar_contradiction_clause,[],[f1320])).

fof(f1320,plain,
    ( $false
    | ~ spl15_7
    | ~ spl15_8
    | spl15_43 ),
    inference(subsumption_resolution,[],[f1319,f78])).

fof(f78,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f1319,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl15_7
    | ~ spl15_8
    | spl15_43 ),
    inference(subsumption_resolution,[],[f1318,f79])).

fof(f1318,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl15_7
    | ~ spl15_8
    | spl15_43 ),
    inference(subsumption_resolution,[],[f1317,f80])).

fof(f1317,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl15_7
    | ~ spl15_8
    | spl15_43 ),
    inference(subsumption_resolution,[],[f1316,f157])).

fof(f157,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl15_8 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl15_8
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).

fof(f1316,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl15_7
    | spl15_43 ),
    inference(subsumption_resolution,[],[f1309,f153])).

fof(f1309,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl15_43 ),
    inference(resolution,[],[f1175,f302])).

fof(f302,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f297])).

fof(f297,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f127,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK13(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK13(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK13(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK13(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f71,f72])).

fof(f72,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK13(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK13(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK13(X0,X1,X2,X3),X1)
        & m1_subset_1(sK13(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
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
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
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
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
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
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
                 => ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_0)).

fof(f1175,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK2)
    | spl15_43 ),
    inference(avatar_component_clause,[],[f1174])).

fof(f1174,plain,
    ( spl15_43
  <=> r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_43])])).

fof(f1225,plain,
    ( ~ spl15_7
    | ~ spl15_8
    | spl15_38 ),
    inference(avatar_contradiction_clause,[],[f1224])).

fof(f1224,plain,
    ( $false
    | ~ spl15_7
    | ~ spl15_8
    | spl15_38 ),
    inference(subsumption_resolution,[],[f1223,f78])).

fof(f1223,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl15_7
    | ~ spl15_8
    | spl15_38 ),
    inference(subsumption_resolution,[],[f1222,f79])).

fof(f1222,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl15_7
    | ~ spl15_8
    | spl15_38 ),
    inference(subsumption_resolution,[],[f1221,f80])).

fof(f1221,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl15_7
    | ~ spl15_8
    | spl15_38 ),
    inference(subsumption_resolution,[],[f1220,f157])).

fof(f1220,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl15_7
    | spl15_38 ),
    inference(subsumption_resolution,[],[f1213,f153])).

fof(f1213,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl15_38 ),
    inference(resolution,[],[f1130,f292])).

fof(f292,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f287])).

fof(f287,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f126,f122])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f1130,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK3)
    | spl15_38 ),
    inference(avatar_component_clause,[],[f1129])).

fof(f1179,plain,
    ( ~ spl15_15
    | ~ spl15_43
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_8
    | spl15_24 ),
    inference(avatar_split_clause,[],[f1178,f749,f156,f148,f140,f1174,f592])).

fof(f140,plain,
    ( spl15_4
  <=> r2_hidden(k7_yellow_3(sK0,sK0,sK2,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f148,plain,
    ( spl15_6
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f749,plain,
    ( spl15_24
  <=> r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_24])])).

fof(f1178,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_8
    | spl15_24 ),
    inference(subsumption_resolution,[],[f1177,f546])).

fof(f546,plain,
    ( r1_orders_2(sK0,sK4,sK4)
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f545,f165])).

fof(f545,plain,
    ( r1_orders_2(sK0,sK4,sK4)
    | v2_struct_0(sK0)
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f544,f77])).

fof(f544,plain,
    ( r1_orders_2(sK0,sK4,sK4)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f543,f80])).

fof(f543,plain,
    ( r1_orders_2(sK0,sK4,sK4)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f542,f149])).

fof(f149,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl15_6 ),
    inference(avatar_component_clause,[],[f148])).

fof(f542,plain,
    ( r1_orders_2(sK0,sK4,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6 ),
    inference(duplicate_literal_removal,[],[f541])).

fof(f541,plain,
    ( r1_orders_2(sK0,sK4,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6 ),
    inference(resolution,[],[f512,f120])).

fof(f512,plain,
    ( r3_orders_2(sK0,sK4,sK4)
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f511,f165])).

fof(f511,plain,
    ( r3_orders_2(sK0,sK4,sK4)
    | v2_struct_0(sK0)
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f510,f77])).

fof(f510,plain,
    ( r3_orders_2(sK0,sK4,sK4)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f508,f80])).

fof(f508,plain,
    ( r3_orders_2(sK0,sK4,sK4)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6 ),
    inference(resolution,[],[f149,f171])).

fof(f1177,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK4,sK4)
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_8
    | spl15_24 ),
    inference(subsumption_resolution,[],[f1155,f149])).

fof(f1155,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK4,sK4)
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_8
    | spl15_24 ),
    inference(resolution,[],[f626,f750])).

fof(f750,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | spl15_24 ),
    inference(avatar_component_clause,[],[f749])).

fof(f626,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X1,X0),sK1)
        | ~ r1_orders_2(sK0,X1,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4,X0) )
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_8 ),
    inference(subsumption_resolution,[],[f625,f157])).

fof(f625,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK4,X0)
        | ~ r1_orders_2(sK0,X1,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X1,X0),sK1) )
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_8 ),
    inference(subsumption_resolution,[],[f624,f149])).

fof(f624,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK4,X0)
        | ~ r1_orders_2(sK0,X1,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X1,X0),sK1) )
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_8 ),
    inference(resolution,[],[f540,f340])).

fof(f540,plain,
    ( r2_hidden(k4_tarski(sK2,sK4),sK1)
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_8 ),
    inference(subsumption_resolution,[],[f539,f165])).

fof(f539,plain,
    ( r2_hidden(k4_tarski(sK2,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_8 ),
    inference(subsumption_resolution,[],[f538,f80])).

fof(f538,plain,
    ( r2_hidden(k4_tarski(sK2,sK4),sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_8 ),
    inference(subsumption_resolution,[],[f537,f157])).

fof(f537,plain,
    ( r2_hidden(k4_tarski(sK2,sK4),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_4
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f536,f149])).

fof(f536,plain,
    ( r2_hidden(k4_tarski(sK2,sK4),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f535])).

fof(f535,plain,
    ( r2_hidden(k4_tarski(sK2,sK4),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_4 ),
    inference(superposition,[],[f141,f124])).

fof(f141,plain,
    ( r2_hidden(k7_yellow_3(sK0,sK0,sK2,sK4),sK1)
    | ~ spl15_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f751,plain,
    ( ~ spl15_15
    | ~ spl15_24
    | ~ spl15_6
    | spl15_19 ),
    inference(avatar_split_clause,[],[f747,f605,f148,f749,f592])).

fof(f605,plain,
    ( spl15_19
  <=> r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_19])])).

fof(f747,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl15_6
    | spl15_19 ),
    inference(subsumption_resolution,[],[f746,f165])).

fof(f746,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl15_6
    | spl15_19 ),
    inference(subsumption_resolution,[],[f745,f80])).

fof(f745,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | spl15_19 ),
    inference(subsumption_resolution,[],[f732,f149])).

fof(f732,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_19 ),
    inference(duplicate_literal_removal,[],[f731])).

fof(f731,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_19 ),
    inference(superposition,[],[f606,f124])).

fof(f606,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | spl15_19 ),
    inference(avatar_component_clause,[],[f605])).

fof(f726,plain,
    ( ~ spl15_15
    | ~ spl15_19
    | ~ spl15_23
    | ~ spl15_1
    | spl15_2
    | ~ spl15_5
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f722,f148,f144,f132,f129,f724,f605,f592])).

fof(f129,plain,
    ( spl15_1
  <=> v5_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f132,plain,
    ( spl15_2
  <=> r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k12_lattice3(sK0,sK4,sK5)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f722,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl15_1
    | spl15_2
    | ~ spl15_5
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f721,f165])).

fof(f721,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl15_1
    | spl15_2
    | ~ spl15_5
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f720,f80])).

fof(f720,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_1
    | spl15_2
    | ~ spl15_5
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f719,f82])).

fof(f719,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_1
    | spl15_2
    | ~ spl15_5
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f718,f159])).

fof(f159,plain,
    ( v5_waybel_7(sK1,sK0)
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f718,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_2
    | ~ spl15_5
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f717,f149])).

fof(f717,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_2
    | ~ spl15_5
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f712,f145])).

fof(f712,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_2
    | ~ spl15_5
    | ~ spl15_6 ),
    inference(resolution,[],[f588,f102])).

fof(f102,plain,(
    ! [X6,X0,X7,X5,X1] :
      ( r2_hidden(k7_yellow_3(X0,X0,X5,k11_lattice3(X0,X6,X7)),X1)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X7),X1)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X6),X1)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_7(X1,X0)
              | ( ~ r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),k11_lattice3(X0,sK11(X0,X1),sK12(X0,X1))),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),sK12(X0,X1)),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),sK11(X0,X1)),X1)
                & m1_subset_1(sK12(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK11(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ! [X7] :
                          ( r2_hidden(k7_yellow_3(X0,X0,X5,k11_lattice3(X0,X6,X7)),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X7),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X6),X1)
                          | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v5_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f63,f66,f65,f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                  & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                  & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),k11_lattice3(X0,X3,X4)),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),X4),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),X3),X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),k11_lattice3(X0,X3,X4)),X1)
              & r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),X4),X1)
              & r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),X3),X1)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ~ r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),k11_lattice3(X0,sK11(X0,X1),X4)),X1)
            & r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),X4),X1)
            & r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),sK11(X0,X1)),X1)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK11(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),k11_lattice3(X0,sK11(X0,X1),X4)),X1)
          & r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),X4),X1)
          & r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),sK11(X0,X1)),X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),k11_lattice3(X0,sK11(X0,X1),sK12(X0,X1))),X1)
        & r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),sK12(X0,X1)),X1)
        & r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),sK11(X0,X1)),X1)
        & m1_subset_1(sK12(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ? [X4] :
                          ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ! [X7] :
                          ( r2_hidden(k7_yellow_3(X0,X0,X5,k11_lattice3(X0,X6,X7)),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X7),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X6),X1)
                          | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v5_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ? [X4] :
                          ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( ! [X4] :
                          ( r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v5_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                        | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                        | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                        | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                        | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
         => ( v5_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1) )
                         => r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_7)).

fof(f588,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k11_lattice3(sK0,sK4,sK5)),sK1)
    | spl15_2
    | ~ spl15_5
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f587,f78])).

fof(f587,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k11_lattice3(sK0,sK4,sK5)),sK1)
    | ~ v5_orders_2(sK0)
    | spl15_2
    | ~ spl15_5
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f586,f79])).

fof(f586,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k11_lattice3(sK0,sK4,sK5)),sK1)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl15_2
    | ~ spl15_5
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f585,f80])).

fof(f585,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k11_lattice3(sK0,sK4,sK5)),sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl15_2
    | ~ spl15_5
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f584,f149])).

fof(f584,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k11_lattice3(sK0,sK4,sK5)),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl15_2
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f553,f145])).

fof(f553,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k11_lattice3(sK0,sK4,sK5)),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl15_2 ),
    inference(superposition,[],[f133,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
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
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f133,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k12_lattice3(sK0,sK4,sK5)),sK1)
    | spl15_2 ),
    inference(avatar_component_clause,[],[f132])).

fof(f642,plain,
    ( ~ spl15_7
    | ~ spl15_8
    | spl15_15 ),
    inference(avatar_contradiction_clause,[],[f641])).

fof(f641,plain,
    ( $false
    | ~ spl15_7
    | ~ spl15_8
    | spl15_15 ),
    inference(subsumption_resolution,[],[f640,f78])).

fof(f640,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl15_7
    | ~ spl15_8
    | spl15_15 ),
    inference(subsumption_resolution,[],[f639,f79])).

fof(f639,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl15_7
    | ~ spl15_8
    | spl15_15 ),
    inference(subsumption_resolution,[],[f638,f80])).

fof(f638,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl15_7
    | ~ spl15_8
    | spl15_15 ),
    inference(subsumption_resolution,[],[f637,f157])).

fof(f637,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl15_7
    | spl15_15 ),
    inference(subsumption_resolution,[],[f633,f153])).

fof(f633,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl15_15 ),
    inference(resolution,[],[f593,f122])).

fof(f593,plain,
    ( ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl15_15 ),
    inference(avatar_component_clause,[],[f592])).

fof(f474,plain,
    ( spl15_1
    | ~ spl15_11 ),
    inference(avatar_contradiction_clause,[],[f473])).

fof(f473,plain,
    ( $false
    | spl15_1
    | ~ spl15_11 ),
    inference(subsumption_resolution,[],[f472,f165])).

fof(f472,plain,
    ( v2_struct_0(sK0)
    | spl15_1
    | ~ spl15_11 ),
    inference(subsumption_resolution,[],[f471,f80])).

fof(f471,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_1
    | ~ spl15_11 ),
    inference(subsumption_resolution,[],[f470,f82])).

fof(f470,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_1
    | ~ spl15_11 ),
    inference(subsumption_resolution,[],[f469,f130])).

fof(f130,plain,
    ( ~ v5_waybel_7(sK1,sK0)
    | spl15_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f469,plain,
    ( v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_1
    | ~ spl15_11 ),
    inference(subsumption_resolution,[],[f468,f189])).

fof(f189,plain,
    ( m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | spl15_1 ),
    inference(subsumption_resolution,[],[f188,f165])).

fof(f188,plain,
    ( m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl15_1 ),
    inference(subsumption_resolution,[],[f187,f80])).

fof(f187,plain,
    ( m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_1 ),
    inference(subsumption_resolution,[],[f185,f130])).

fof(f185,plain,
    ( m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f103,f82])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | v5_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f468,plain,
    ( ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_1
    | ~ spl15_11 ),
    inference(subsumption_resolution,[],[f464,f204])).

fof(f204,plain,
    ( r3_orders_2(sK0,sK10(sK0,sK1),sK10(sK0,sK1))
    | spl15_1 ),
    inference(subsumption_resolution,[],[f203,f165])).

fof(f203,plain,
    ( r3_orders_2(sK0,sK10(sK0,sK1),sK10(sK0,sK1))
    | v2_struct_0(sK0)
    | spl15_1 ),
    inference(subsumption_resolution,[],[f202,f77])).

fof(f202,plain,
    ( r3_orders_2(sK0,sK10(sK0,sK1),sK10(sK0,sK1))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_1 ),
    inference(subsumption_resolution,[],[f200,f80])).

fof(f200,plain,
    ( r3_orders_2(sK0,sK10(sK0,sK1),sK10(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_1 ),
    inference(resolution,[],[f189,f171])).

fof(f464,plain,
    ( ~ r3_orders_2(sK0,sK10(sK0,sK1),sK10(sK0,sK1))
    | ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_11 ),
    inference(resolution,[],[f423,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),sK12(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f423,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK12(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK10(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_11 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl15_11
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,sK10(sK0,sK1),X0)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK12(sK0,sK1)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_11])])).

fof(f446,plain,
    ( spl15_1
    | spl15_10 ),
    inference(avatar_contradiction_clause,[],[f445])).

fof(f445,plain,
    ( $false
    | spl15_1
    | spl15_10 ),
    inference(subsumption_resolution,[],[f444,f165])).

fof(f444,plain,
    ( v2_struct_0(sK0)
    | spl15_1
    | spl15_10 ),
    inference(subsumption_resolution,[],[f443,f80])).

fof(f443,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_1
    | spl15_10 ),
    inference(subsumption_resolution,[],[f442,f82])).

fof(f442,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_1
    | spl15_10 ),
    inference(subsumption_resolution,[],[f439,f130])).

fof(f439,plain,
    ( v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_10 ),
    inference(resolution,[],[f420,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),sK11(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f420,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,sK10(sK0,sK1),sK11(sK0,sK1)),sK1)
    | spl15_10 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl15_10
  <=> r2_hidden(k7_yellow_3(sK0,sK0,sK10(sK0,sK1),sK11(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_10])])).

fof(f424,plain,
    ( ~ spl15_10
    | spl15_11
    | spl15_1
    | ~ spl15_9 ),
    inference(avatar_split_clause,[],[f417,f161,f129,f422,f419])).

fof(f161,plain,
    ( spl15_9
  <=> ! [X9,X7,X8,X6] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X6,X7),k12_lattice3(sK0,X8,X9)),sK1)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X6,X8),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X7,X9),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_9])])).

fof(f417,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK10(sK0,sK1),sK11(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK12(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK10(sK0,sK1),X0) )
    | spl15_1
    | ~ spl15_9 ),
    inference(subsumption_resolution,[],[f416,f165])).

fof(f416,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK10(sK0,sK1),sK11(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK12(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK10(sK0,sK1),X0)
        | v2_struct_0(sK0) )
    | spl15_1
    | ~ spl15_9 ),
    inference(subsumption_resolution,[],[f415,f80])).

fof(f415,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK10(sK0,sK1),sK11(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK12(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK10(sK0,sK1),X0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl15_1
    | ~ spl15_9 ),
    inference(subsumption_resolution,[],[f414,f82])).

fof(f414,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK10(sK0,sK1),sK11(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK12(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK10(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl15_1
    | ~ spl15_9 ),
    inference(subsumption_resolution,[],[f413,f130])).

fof(f413,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK10(sK0,sK1),sK11(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK12(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK10(sK0,sK1),X0)
        | v5_waybel_7(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl15_1
    | ~ spl15_9 ),
    inference(subsumption_resolution,[],[f412,f199])).

fof(f199,plain,
    ( m1_subset_1(sK12(sK0,sK1),u1_struct_0(sK0))
    | spl15_1 ),
    inference(subsumption_resolution,[],[f198,f165])).

fof(f198,plain,
    ( m1_subset_1(sK12(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl15_1 ),
    inference(subsumption_resolution,[],[f197,f80])).

fof(f197,plain,
    ( m1_subset_1(sK12(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_1 ),
    inference(subsumption_resolution,[],[f195,f130])).

fof(f195,plain,
    ( m1_subset_1(sK12(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f105,f82])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | m1_subset_1(sK12(X0,X1),u1_struct_0(X0))
      | v5_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f412,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK12(sK0,sK1),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK10(sK0,sK1),sK11(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK12(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK10(sK0,sK1),X0)
        | v5_waybel_7(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl15_1
    | ~ spl15_9 ),
    inference(subsumption_resolution,[],[f411,f194])).

fof(f194,plain,
    ( m1_subset_1(sK11(sK0,sK1),u1_struct_0(sK0))
    | spl15_1 ),
    inference(subsumption_resolution,[],[f193,f165])).

fof(f193,plain,
    ( m1_subset_1(sK11(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl15_1 ),
    inference(subsumption_resolution,[],[f192,f80])).

fof(f192,plain,
    ( m1_subset_1(sK11(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl15_1 ),
    inference(subsumption_resolution,[],[f190,f130])).

fof(f190,plain,
    ( m1_subset_1(sK11(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f104,f82])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | m1_subset_1(sK11(X0,X1),u1_struct_0(X0))
      | v5_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f411,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK11(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK12(sK0,sK1),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK10(sK0,sK1),sK11(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK12(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK10(sK0,sK1),X0)
        | v5_waybel_7(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl15_1
    | ~ spl15_9 ),
    inference(subsumption_resolution,[],[f408,f189])).

fof(f408,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK11(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK12(sK0,sK1),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK10(sK0,sK1),sK11(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK12(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK10(sK0,sK1),X0)
        | v5_waybel_7(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_9 ),
    inference(resolution,[],[f355,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k7_yellow_3(X0,X0,sK10(X0,X1),k11_lattice3(X0,sK11(X0,X1),sK12(X0,X1))),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f355,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,X0,k11_lattice3(sK0,X2,X3)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,X2),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,X3),sK1)
        | ~ r3_orders_2(sK0,X0,X1) )
    | ~ spl15_9 ),
    inference(subsumption_resolution,[],[f354,f77])).

fof(f354,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,X0,k11_lattice3(sK0,X2,X3)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,X2),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,X3),sK1)
        | ~ r3_orders_2(sK0,X0,X1)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_9 ),
    inference(subsumption_resolution,[],[f353,f78])).

fof(f353,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,X0,k11_lattice3(sK0,X2,X3)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,X2),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,X3),sK1)
        | ~ r3_orders_2(sK0,X0,X1)
        | ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_9 ),
    inference(subsumption_resolution,[],[f352,f79])).

fof(f352,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,X0,k11_lattice3(sK0,X2,X3)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,X2),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,X3),sK1)
        | ~ r3_orders_2(sK0,X0,X1)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_9 ),
    inference(subsumption_resolution,[],[f351,f80])).

fof(f351,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,X0,k11_lattice3(sK0,X2,X3)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,X2),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,X3),sK1)
        | ~ r3_orders_2(sK0,X0,X1)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_9 ),
    inference(duplicate_literal_removal,[],[f346])).

fof(f346,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,X0,k11_lattice3(sK0,X2,X3)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,X2),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,X3),sK1)
        | ~ r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_9 ),
    inference(superposition,[],[f231,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = X1
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_0)).

fof(f231,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X2,X3),k11_lattice3(sK0,X0,X1)),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,X0),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X3,X1),sK1) )
    | ~ spl15_9 ),
    inference(subsumption_resolution,[],[f230,f78])).

fof(f230,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X2,X3),k11_lattice3(sK0,X0,X1)),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,X0),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X3,X1),sK1)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_9 ),
    inference(subsumption_resolution,[],[f229,f79])).

fof(f229,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X2,X3),k11_lattice3(sK0,X0,X1)),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,X0),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X3,X1),sK1)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_9 ),
    inference(subsumption_resolution,[],[f228,f80])).

fof(f228,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X2,X3),k11_lattice3(sK0,X0,X1)),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,X0),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X3,X1),sK1)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_9 ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X2,X3),k11_lattice3(sK0,X0,X1)),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,X0),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X3,X1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_9 ),
    inference(superposition,[],[f162,f123])).

fof(f162,plain,
    ( ! [X6,X8,X7,X9] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X6,X7),k12_lattice3(sK0,X8,X9)),sK1)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X6,X8),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X7,X9),sK1) )
    | ~ spl15_9 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,
    ( spl15_1
    | spl15_9 ),
    inference(avatar_split_clause,[],[f83,f161,f129])).

fof(f83,plain,(
    ! [X6,X8,X7,X9] :
      ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X6,X7),k12_lattice3(sK0,X8,X9)),sK1)
      | ~ r2_hidden(k7_yellow_3(sK0,sK0,X7,X9),sK1)
      | ~ r2_hidden(k7_yellow_3(sK0,sK0,X6,X8),sK1)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v5_waybel_7(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f158,plain,
    ( ~ spl15_1
    | spl15_8 ),
    inference(avatar_split_clause,[],[f84,f156,f129])).

fof(f84,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f154,plain,
    ( ~ spl15_1
    | spl15_7 ),
    inference(avatar_split_clause,[],[f85,f152,f129])).

fof(f85,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f150,plain,
    ( ~ spl15_1
    | spl15_6 ),
    inference(avatar_split_clause,[],[f86,f148,f129])).

fof(f86,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f146,plain,
    ( ~ spl15_1
    | spl15_5 ),
    inference(avatar_split_clause,[],[f87,f144,f129])).

fof(f87,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f142,plain,
    ( ~ spl15_1
    | spl15_4 ),
    inference(avatar_split_clause,[],[f88,f140,f129])).

fof(f88,plain,
    ( r2_hidden(k7_yellow_3(sK0,sK0,sK2,sK4),sK1)
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f138,plain,
    ( ~ spl15_1
    | spl15_3 ),
    inference(avatar_split_clause,[],[f89,f136,f129])).

fof(f89,plain,
    ( r2_hidden(k7_yellow_3(sK0,sK0,sK3,sK5),sK1)
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f134,plain,
    ( ~ spl15_1
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f90,f132,f129])).

fof(f90,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k12_lattice3(sK0,sK4,sK5)),sK1)
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

%------------------------------------------------------------------------------
