%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1685+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  317 (2828 expanded)
%              Number of leaves         :   35 (1574 expanded)
%              Depth                    :   34
%              Number of atoms          : 1823 (62602 expanded)
%              Number of equality atoms :  244 (8123 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1096,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f117,f122,f123,f224,f246,f253,f257,f269,f302,f306,f485,f501,f897,f1095])).

fof(f1095,plain,
    ( spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_25
    | ~ spl8_30 ),
    inference(avatar_contradiction_clause,[],[f1094])).

fof(f1094,plain,
    ( $false
    | spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_25
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f1093,f1045])).

fof(f1045,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f1044,f143])).

fof(f143,plain,(
    ! [X0] : k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(resolution,[],[f98,f67])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ( ~ r3_waybel_0(sK2,sK3,sK5,sK7)
        & r3_waybel_0(sK0,sK1,sK4,sK6) )
      | ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
        & r4_waybel_0(sK0,sK1,sK4,sK6) ) )
    & sK6 = sK7
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    & l1_orders_2(sK3)
    & ~ v2_struct_0(sK3)
    & l1_orders_2(sK2)
    & ~ v2_struct_0(sK2)
    & l1_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f18,f48,f47,f46,f45,f44,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                                        & r3_waybel_0(X0,X1,X4,X6) )
                                      | ( ~ r4_waybel_0(X2,X3,X5,X7)
                                        & r4_waybel_0(X0,X1,X4,X6) ) )
                                    & X6 = X7
                                    & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                                & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                            & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                    & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                    & l1_orders_2(X3)
                    & ~ v2_struct_0(X3) )
                & l1_orders_2(X2)
                & ~ v2_struct_0(X2) )
            & l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                                      & r3_waybel_0(sK0,X1,X4,X6) )
                                    | ( ~ r4_waybel_0(X2,X3,X5,X7)
                                      & r4_waybel_0(sK0,X1,X4,X6) ) )
                                  & X6 = X7
                                  & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
                          & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                  & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
                  & l1_orders_2(X3)
                  & ~ v2_struct_0(X3) )
              & l1_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                                    & r3_waybel_0(sK0,X1,X4,X6) )
                                  | ( ~ r4_waybel_0(X2,X3,X5,X7)
                                    & r4_waybel_0(sK0,X1,X4,X6) ) )
                                & X6 = X7
                                & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                            & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
                        & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
                & l1_orders_2(X3)
                & ~ v2_struct_0(X3) )
            & l1_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                                  & r3_waybel_0(sK0,sK1,X4,X6) )
                                | ( ~ r4_waybel_0(X2,X3,X5,X7)
                                  & r4_waybel_0(sK0,sK1,X4,X6) ) )
                              & X6 = X7
                              & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
                      & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
              & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
              & l1_orders_2(X3)
              & ~ v2_struct_0(X3) )
          & l1_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & l1_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                                & r3_waybel_0(sK0,sK1,X4,X6) )
                              | ( ~ r4_waybel_0(X2,X3,X5,X7)
                                & r4_waybel_0(sK0,sK1,X4,X6) ) )
                            & X6 = X7
                            & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                        & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
                    & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                    & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
            & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
            & l1_orders_2(X3)
            & ~ v2_struct_0(X3) )
        & l1_orders_2(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ( ~ r3_waybel_0(sK2,X3,X5,X7)
                              & r3_waybel_0(sK0,sK1,X4,X6) )
                            | ( ~ r4_waybel_0(sK2,X3,X5,X7)
                              & r4_waybel_0(sK0,sK1,X4,X6) ) )
                          & X6 = X7
                          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) )
                      & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
                  & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(X3),X4,X5)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
                  & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X3))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
          & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
          & l1_orders_2(X3)
          & ~ v2_struct_0(X3) )
      & l1_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ( ~ r3_waybel_0(sK2,X3,X5,X7)
                            & r3_waybel_0(sK0,sK1,X4,X6) )
                          | ( ~ r4_waybel_0(sK2,X3,X5,X7)
                            & r4_waybel_0(sK0,sK1,X4,X6) ) )
                        & X6 = X7
                        & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) )
                    & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
                & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(X3),X4,X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
                & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X3))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
        & l1_orders_2(X3)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ( ~ r3_waybel_0(sK2,sK3,X5,X7)
                          & r3_waybel_0(sK0,sK1,X4,X6) )
                        | ( ~ r4_waybel_0(sK2,sK3,X5,X7)
                          & r4_waybel_0(sK0,sK1,X4,X6) ) )
                      & X6 = X7
                      & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) )
                  & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
              & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),X4,X5)
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK3))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
      & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      & l1_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ( ~ r3_waybel_0(sK2,sK3,X5,X7)
                        & r3_waybel_0(sK0,sK1,X4,X6) )
                      | ( ~ r4_waybel_0(sK2,sK3,X5,X7)
                        & r4_waybel_0(sK0,sK1,X4,X6) ) )
                    & X6 = X7
                    & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) )
                & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
            & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),X4,X5)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK3))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ( ~ r3_waybel_0(sK2,sK3,X5,X7)
                      & r3_waybel_0(sK0,sK1,sK4,X6) )
                    | ( ~ r4_waybel_0(sK2,sK3,X5,X7)
                      & r4_waybel_0(sK0,sK1,sK4,X6) ) )
                  & X6 = X7
                  & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) )
              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
          & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),sK4,X5)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ( ( ~ r3_waybel_0(sK2,sK3,X5,X7)
                    & r3_waybel_0(sK0,sK1,sK4,X6) )
                  | ( ~ r4_waybel_0(sK2,sK3,X5,X7)
                    & r4_waybel_0(sK0,sK1,sK4,X6) ) )
                & X6 = X7
                & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) )
            & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
        & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),sK4,X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X5) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ( ( ~ r3_waybel_0(sK2,sK3,sK5,X7)
                  & r3_waybel_0(sK0,sK1,sK4,X6) )
                | ( ~ r4_waybel_0(sK2,sK3,sK5,X7)
                  & r4_waybel_0(sK0,sK1,sK4,X6) ) )
              & X6 = X7
              & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
      & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ( ( ~ r3_waybel_0(sK2,sK3,sK5,X7)
                & r3_waybel_0(sK0,sK1,sK4,X6) )
              | ( ~ r4_waybel_0(sK2,sK3,sK5,X7)
                & r4_waybel_0(sK0,sK1,sK4,X6) ) )
            & X6 = X7
            & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X7] :
          ( ( ( ~ r3_waybel_0(sK2,sK3,sK5,X7)
              & r3_waybel_0(sK0,sK1,sK4,sK6) )
            | ( ~ r4_waybel_0(sK2,sK3,sK5,X7)
              & r4_waybel_0(sK0,sK1,sK4,sK6) ) )
          & sK6 = X7
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X7] :
        ( ( ( ~ r3_waybel_0(sK2,sK3,sK5,X7)
            & r3_waybel_0(sK0,sK1,sK4,sK6) )
          | ( ~ r4_waybel_0(sK2,sK3,sK5,X7)
            & r4_waybel_0(sK0,sK1,sK4,sK6) ) )
        & sK6 = X7
        & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( ( ~ r3_waybel_0(sK2,sK3,sK5,sK7)
          & r3_waybel_0(sK0,sK1,sK4,sK6) )
        | ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
          & r4_waybel_0(sK0,sK1,sK4,sK6) ) )
      & sK6 = sK7
      & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                                      & r3_waybel_0(X0,X1,X4,X6) )
                                    | ( ~ r4_waybel_0(X2,X3,X5,X7)
                                      & r4_waybel_0(X0,X1,X4,X6) ) )
                                  & X6 = X7
                                  & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                  & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                  & l1_orders_2(X3)
                  & ~ v2_struct_0(X3) )
              & l1_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                                      & r3_waybel_0(X0,X1,X4,X6) )
                                    | ( ~ r4_waybel_0(X2,X3,X5,X7)
                                      & r4_waybel_0(X0,X1,X4,X6) ) )
                                  & X6 = X7
                                  & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                  & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                  & l1_orders_2(X3)
                  & ~ v2_struct_0(X3) )
              & l1_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( l1_orders_2(X3)
                      & ~ v2_struct_0(X3) )
                   => ( ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                        & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                                & v1_funct_1(X5) )
                             => ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                               => ! [X6] :
                                    ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
                                   => ! [X7] :
                                        ( m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))
                                       => ( X6 = X7
                                         => ( ( r3_waybel_0(X0,X1,X4,X6)
                                             => r3_waybel_0(X2,X3,X5,X7) )
                                            & ( r4_waybel_0(X0,X1,X4,X6)
                                             => r4_waybel_0(X2,X3,X5,X7) ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( l1_orders_2(X3)
                    & ~ v2_struct_0(X3) )
                 => ( ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                      & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(X5) )
                           => ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                             => ! [X6] :
                                  ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))
                                     => ( X6 = X7
                                       => ( ( r3_waybel_0(X0,X1,X4,X6)
                                           => r3_waybel_0(X2,X3,X5,X7) )
                                          & ( r4_waybel_0(X0,X1,X4,X6)
                                           => r4_waybel_0(X2,X3,X5,X7) ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_waybel_0)).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f1044,plain,
    ( k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f1043,f784])).

fof(f784,plain,
    ( ! [X0] : k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0)) = k1_funct_1(sK4,k2_yellow_0(sK0,X0))
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f783,f66])).

fof(f66,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f783,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0)) = k1_funct_1(sK4,k2_yellow_0(sK0,X0)) )
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f781,f65])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f781,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0)) = k1_funct_1(sK4,k2_yellow_0(sK0,X0)) )
    | ~ spl8_30 ),
    inference(resolution,[],[f305,f67])).

fof(f305,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),X0)
        | k3_funct_2(u1_struct_0(sK0),X0,X1,k2_yellow_0(sK0,X2)) = k1_funct_1(X1,k2_yellow_0(sK0,X2)) )
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl8_30
  <=> ! [X1,X0,X2] :
        ( k3_funct_2(u1_struct_0(sK0),X0,X1,k2_yellow_0(sK0,X2)) = k1_funct_1(X1,k2_yellow_0(sK0,X2))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f1043,plain,
    ( k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6))
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1042,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f1042,plain,
    ( k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6))
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1041,f56])).

fof(f56,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f1041,plain,
    ( k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1040,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f1040,plain,
    ( k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1039,f58])).

fof(f58,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f1039,plain,
    ( k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1038,f65])).

fof(f1038,plain,
    ( k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1037,f66])).

fof(f1037,plain,
    ( k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1036,f67])).

fof(f1036,plain,
    ( k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1035,f72])).

fof(f72,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f1035,plain,
    ( k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1033,f602])).

fof(f602,plain,
    ( r2_yellow_0(sK0,sK6)
    | ~ spl8_20 ),
    inference(trivial_inequality_removal,[],[f598])).

fof(f598,plain,
    ( r2_yellow_0(sK0,sK6)
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ spl8_20 ),
    inference(resolution,[],[f491,f56])).

fof(f491,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(X1)
        | r2_yellow_0(X1,sK6)
        | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) )
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f490,f63])).

fof(f63,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f490,plain,
    ( ! [X1] :
        ( r2_yellow_0(X1,sK6)
        | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
        | ~ l1_orders_2(X1) )
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f487,f60])).

fof(f60,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f487,plain,
    ( ! [X1] :
        ( r2_yellow_0(X1,sK6)
        | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
        | ~ l1_orders_2(X1)
        | ~ l1_orders_2(sK2) )
    | ~ spl8_20 ),
    inference(resolution,[],[f223,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X2)
      | r2_yellow_0(X1,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X0,X2) )
              & ( r1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X0,X2) ) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X0,X2) )
              & ( r1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X0,X2) ) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( ( r2_yellow_0(X0,X2)
                 => r2_yellow_0(X1,X2) )
                & ( r1_yellow_0(X0,X2)
                 => r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_0)).

fof(f223,plain,
    ( r2_yellow_0(sK2,sK6)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl8_20
  <=> r2_yellow_0(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f1033,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4 ),
    inference(resolution,[],[f121,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_waybel_0(X0,X1,X2,X3)
      | ~ r2_yellow_0(X0,X3)
      | k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r3_waybel_0(X0,X1,X2,X3)
                      | ( ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
                          | ~ r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                        & r2_yellow_0(X0,X3) ) )
                    & ( ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
                        & r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r2_yellow_0(X0,X3)
                      | ~ r3_waybel_0(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r3_waybel_0(X0,X1,X2,X3)
                      | ( ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
                          | ~ r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                        & r2_yellow_0(X0,X3) ) )
                    & ( ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
                        & r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r2_yellow_0(X0,X3)
                      | ~ r3_waybel_0(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r3_waybel_0(X0,X1,X2,X3)
                  <=> ( ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
                        & r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r2_yellow_0(X0,X3) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r3_waybel_0(X0,X1,X2,X3)
                  <=> ( ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
                        & r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r2_yellow_0(X0,X3) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r3_waybel_0(X0,X1,X2,X3)
                  <=> ( r2_yellow_0(X0,X3)
                     => ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
                        & r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d30_waybel_0)).

fof(f121,plain,
    ( r3_waybel_0(sK0,sK1,sK4,sK6)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl8_4
  <=> r3_waybel_0(sK0,sK1,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f1093,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_25
    | ~ spl8_30 ),
    inference(superposition,[],[f1082,f784])).

fof(f1082,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) != k2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f1081,f544])).

fof(f544,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK2) ),
    inference(trivial_inequality_removal,[],[f541])).

fof(f541,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK2) ),
    inference(superposition,[],[f315,f63])).

fof(f315,plain,(
    ! [X6,X5] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X5,X6)
      | u1_struct_0(sK0) = X5 ) ),
    inference(resolution,[],[f139,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f139,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f80,f56])).

fof(f80,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f1081,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6))
    | spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f1080,f562])).

fof(f562,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK3) ),
    inference(trivial_inequality_removal,[],[f560])).

fof(f560,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | u1_struct_0(sK1) = u1_struct_0(sK3) ),
    inference(superposition,[],[f341,f64])).

fof(f64,plain,(
    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f341,plain,(
    ! [X6,X5] :
      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X5,X6)
      | u1_struct_0(sK1) = X5 ) ),
    inference(resolution,[],[f140,f96])).

fof(f140,plain,(
    m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f80,f58])).

fof(f1080,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_yellow_0(sK0,sK6))
    | spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f1079,f672])).

fof(f672,plain,
    ( k2_yellow_0(sK2,sK6) = k2_yellow_0(sK0,sK6)
    | ~ spl8_20 ),
    inference(trivial_inequality_removal,[],[f668])).

fof(f668,plain,
    ( k2_yellow_0(sK2,sK6) = k2_yellow_0(sK0,sK6)
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ spl8_20 ),
    inference(resolution,[],[f489,f56])).

fof(f489,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(X0)
        | k2_yellow_0(sK2,sK6) = k2_yellow_0(X0,sK6)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) )
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f488,f63])).

fof(f488,plain,
    ( ! [X0] :
        ( k2_yellow_0(sK2,sK6) = k2_yellow_0(X0,sK6)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
        | ~ l1_orders_2(X0) )
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f486,f60])).

fof(f486,plain,
    ( ! [X0] :
        ( k2_yellow_0(sK2,sK6) = k2_yellow_0(X0,sK6)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK2) )
    | ~ spl8_20 ),
    inference(resolution,[],[f223,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
              | ~ r2_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
              | ~ r2_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r2_yellow_0(X0,X2)
               => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_0)).

fof(f1079,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_yellow_0(sK2,sK6))
    | spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f1078,f1073])).

fof(f1073,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1071,f64])).

fof(f1071,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(resolution,[],[f1059,f62])).

fof(f62,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f1059,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(X0,k9_relat_1(sK4,sK6)) )
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1057,f58])).

fof(f1057,plain,
    ( ! [X0] :
        ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(X0,k9_relat_1(sK4,sK6))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1) )
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(resolution,[],[f1055,f84])).

fof(f1055,plain,
    ( r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f1054,f143])).

fof(f1054,plain,
    ( r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1053,f55])).

fof(f1053,plain,
    ( r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1052,f56])).

fof(f1052,plain,
    ( r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1051,f57])).

fof(f1051,plain,
    ( r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1050,f58])).

fof(f1050,plain,
    ( r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1049,f65])).

fof(f1049,plain,
    ( r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1048,f66])).

fof(f1048,plain,
    ( r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1047,f67])).

fof(f1047,plain,
    ( r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1046,f72])).

fof(f1046,plain,
    ( r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1034,f602])).

fof(f1034,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4 ),
    inference(resolution,[],[f121,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_waybel_0(X0,X1,X2,X3)
      | ~ r2_yellow_0(X0,X3)
      | r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1078,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_yellow_0(sK2,sK6)) != k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f1077,f124])).

fof(f124,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f73,f74])).

fof(f74,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f1077,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_yellow_0(sK2,sK6)) != k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f1074,f274])).

fof(f274,plain,
    ( ~ r3_waybel_0(sK2,sK3,sK4,sK6)
    | spl8_2
    | ~ spl8_25 ),
    inference(superposition,[],[f125,f268])).

fof(f268,plain,
    ( sK4 = sK5
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl8_25
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f125,plain,
    ( ~ r3_waybel_0(sK2,sK3,sK5,sK6)
    | spl8_2 ),
    inference(forward_demodulation,[],[f111,f74])).

fof(f111,plain,
    ( ~ r3_waybel_0(sK2,sK3,sK5,sK7)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl8_2
  <=> r3_waybel_0(sK2,sK3,sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1074,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_yellow_0(sK2,sK6)) != k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r3_waybel_0(sK2,sK3,sK4,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_25 ),
    inference(resolution,[],[f1067,f461])).

fof(f461,plain,
    ( ! [X1] :
        ( ~ r2_yellow_0(sK3,k9_relat_1(sK4,X1))
        | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_yellow_0(sK2,X1)) != k2_yellow_0(sK3,k9_relat_1(sK4,X1))
        | r3_waybel_0(sK2,sK3,sK4,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f460,f268])).

fof(f460,plain,
    ( ! [X1] :
        ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_yellow_0(sK2,X1)) != k2_yellow_0(sK3,k9_relat_1(sK4,X1))
        | ~ r2_yellow_0(sK3,k9_relat_1(sK4,X1))
        | r3_waybel_0(sK2,sK3,sK5,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f459,f268])).

fof(f459,plain,
    ( ! [X1] :
        ( ~ r2_yellow_0(sK3,k9_relat_1(sK4,X1))
        | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,X1)) != k2_yellow_0(sK3,k9_relat_1(sK5,X1))
        | r3_waybel_0(sK2,sK3,sK5,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f458,f268])).

fof(f458,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK5,X1))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,X1)) != k2_yellow_0(sK3,k9_relat_1(sK5,X1))
      | r3_waybel_0(sK2,sK3,sK5,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f457,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f457,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK5,X1))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,X1)) != k2_yellow_0(sK3,k9_relat_1(sK5,X1))
      | r3_waybel_0(sK2,sK3,sK5,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f456,f60])).

fof(f456,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK5,X1))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,X1)) != k2_yellow_0(sK3,k9_relat_1(sK5,X1))
      | r3_waybel_0(sK2,sK3,sK5,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f455,f61])).

fof(f61,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f455,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK5,X1))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,X1)) != k2_yellow_0(sK3,k9_relat_1(sK5,X1))
      | r3_waybel_0(sK2,sK3,sK5,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK3)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f454,f62])).

fof(f454,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK5,X1))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,X1)) != k2_yellow_0(sK3,k9_relat_1(sK5,X1))
      | r3_waybel_0(sK2,sK3,sK5,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f453,f68])).

fof(f68,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f453,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK5,X1))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,X1)) != k2_yellow_0(sK3,k9_relat_1(sK5,X1))
      | r3_waybel_0(sK2,sK3,sK5,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v1_funct_1(sK5)
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f452,f69])).

fof(f69,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f452,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK5,X1))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,X1)) != k2_yellow_0(sK3,k9_relat_1(sK5,X1))
      | r3_waybel_0(sK2,sK3,sK5,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK5)
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f441,f70])).

fof(f70,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f49])).

fof(f441,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK5,X1))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,X1)) != k2_yellow_0(sK3,k9_relat_1(sK5,X1))
      | r3_waybel_0(sK2,sK3,sK5,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK5)
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f89,f144])).

fof(f144,plain,(
    ! [X1] : k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X1) = k9_relat_1(sK5,X1) ),
    inference(resolution,[],[f98,f70])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
      | r3_waybel_0(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1067,plain,
    ( r2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1064,f64])).

fof(f1064,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | r2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(resolution,[],[f1060,f62])).

fof(f1060,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(X1)
        | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        | r2_yellow_0(X1,k9_relat_1(sK4,sK6)) )
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1058,f58])).

fof(f1058,plain,
    ( ! [X1] :
        ( r2_yellow_0(X1,k9_relat_1(sK4,sK6))
        | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        | ~ l1_orders_2(X1)
        | ~ l1_orders_2(sK1) )
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(resolution,[],[f1055,f82])).

fof(f897,plain,
    ( spl8_1
    | ~ spl8_3
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(avatar_contradiction_clause,[],[f896])).

fof(f896,plain,
    ( $false
    | spl8_1
    | ~ spl8_3
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f895,f643])).

fof(f643,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6)) = k1_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(forward_demodulation,[],[f642,f143])).

fof(f642,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6))
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f641,f55])).

fof(f641,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6))
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f640,f56])).

fof(f640,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f639,f57])).

fof(f639,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f638,f58])).

fof(f638,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f637,f65])).

fof(f637,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f636,f66])).

fof(f636,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f635,f67])).

fof(f635,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f634,f72])).

fof(f634,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f249,f630])).

fof(f630,plain,
    ( r1_yellow_0(sK0,sK6)
    | ~ spl8_24 ),
    inference(trivial_inequality_removal,[],[f626])).

fof(f626,plain,
    ( r1_yellow_0(sK0,sK6)
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ spl8_24 ),
    inference(resolution,[],[f507,f56])).

fof(f507,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(X1)
        | r1_yellow_0(X1,sK6)
        | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) )
    | ~ spl8_24 ),
    inference(forward_demodulation,[],[f506,f63])).

fof(f506,plain,
    ( ! [X1] :
        ( r1_yellow_0(X1,sK6)
        | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
        | ~ l1_orders_2(X1) )
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f503,f60])).

fof(f503,plain,
    ( ! [X1] :
        ( r1_yellow_0(X1,sK6)
        | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
        | ~ l1_orders_2(X1)
        | ~ l1_orders_2(sK2) )
    | ~ spl8_24 ),
    inference(resolution,[],[f245,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,X2)
      | r1_yellow_0(X1,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f245,plain,
    ( r1_yellow_0(sK2,sK6)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl8_24
  <=> r1_yellow_0(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f249,plain,
    ( ~ r1_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3 ),
    inference(resolution,[],[f91,f116])).

fof(f116,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl8_3
  <=> r4_waybel_0(sK0,sK1,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_waybel_0(X0,X1,X2,X3)
      | ~ r1_yellow_0(X0,X3)
      | k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r4_waybel_0(X0,X1,X2,X3)
                      | ( ( k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3))
                          | ~ r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                        & r1_yellow_0(X0,X3) ) )
                    & ( ( k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3))
                        & r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_yellow_0(X0,X3)
                      | ~ r4_waybel_0(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r4_waybel_0(X0,X1,X2,X3)
                      | ( ( k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3))
                          | ~ r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                        & r1_yellow_0(X0,X3) ) )
                    & ( ( k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3))
                        & r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_yellow_0(X0,X3)
                      | ~ r4_waybel_0(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

% (25894)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r4_waybel_0(X0,X1,X2,X3)
                  <=> ( ( k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3))
                        & r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_yellow_0(X0,X3) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r4_waybel_0(X0,X1,X2,X3)
                  <=> ( ( k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3))
                        & r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_yellow_0(X0,X3) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r4_waybel_0(X0,X1,X2,X3)
                  <=> ( r1_yellow_0(X0,X3)
                     => ( k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3))
                        & r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d31_waybel_0)).

fof(f895,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6)) != k1_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | spl8_1
    | ~ spl8_3
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f894,f694])).

fof(f694,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f692,f64])).

fof(f692,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(resolution,[],[f659,f62])).

fof(f659,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(X0,k9_relat_1(sK4,sK6)) )
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f657,f58])).

fof(f657,plain,
    ( ! [X0] :
        ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(X0,k9_relat_1(sK4,sK6))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1) )
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(resolution,[],[f653,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
              | ~ r1_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
              | ~ r1_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r1_yellow_0(X0,X2)
               => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_0)).

fof(f653,plain,
    ( r1_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(forward_demodulation,[],[f652,f143])).

fof(f652,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f651,f55])).

fof(f651,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f650,f56])).

fof(f650,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f649,f57])).

fof(f649,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f648,f58])).

fof(f648,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f647,f65])).

fof(f647,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f646,f66])).

fof(f646,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f645,f67])).

fof(f645,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f644,f72])).

fof(f644,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f248,f630])).

fof(f248,plain,
    ( ~ r1_yellow_0(sK0,sK6)
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3 ),
    inference(resolution,[],[f90,f116])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_waybel_0(X0,X1,X2,X3)
      | ~ r1_yellow_0(X0,X3)
      | r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f894,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6)) != k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | spl8_1
    | ~ spl8_3
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f893,f544])).

fof(f893,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6))
    | spl8_1
    | ~ spl8_3
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f892,f562])).

fof(f892,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_yellow_0(sK0,sK6))
    | spl8_1
    | ~ spl8_3
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f891,f680])).

fof(f680,plain,
    ( k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6)
    | ~ spl8_24 ),
    inference(trivial_inequality_removal,[],[f676])).

fof(f676,plain,
    ( k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6)
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ spl8_24 ),
    inference(resolution,[],[f505,f56])).

fof(f505,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(X0)
        | k1_yellow_0(sK2,sK6) = k1_yellow_0(X0,sK6)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) )
    | ~ spl8_24 ),
    inference(forward_demodulation,[],[f504,f63])).

fof(f504,plain,
    ( ! [X0] :
        ( k1_yellow_0(sK2,sK6) = k1_yellow_0(X0,sK6)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
        | ~ l1_orders_2(X0) )
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f502,f60])).

fof(f502,plain,
    ( ! [X0] :
        ( k1_yellow_0(sK2,sK6) = k1_yellow_0(X0,sK6)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK2) )
    | ~ spl8_24 ),
    inference(resolution,[],[f245,f83])).

fof(f891,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_yellow_0(sK2,sK6))
    | spl8_1
    | ~ spl8_3
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f890,f124])).

fof(f890,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_yellow_0(sK2,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl8_1
    | ~ spl8_3
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f887,f275])).

fof(f275,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK4,sK6)
    | spl8_1
    | ~ spl8_25 ),
    inference(superposition,[],[f126,f268])).

fof(f126,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK6)
    | spl8_1 ),
    inference(forward_demodulation,[],[f107,f74])).

fof(f107,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl8_1
  <=> r4_waybel_0(sK2,sK3,sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f887,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_yellow_0(sK2,sK6))
    | r4_waybel_0(sK2,sK3,sK4,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_3
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(resolution,[],[f667,f451])).

fof(f451,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
        | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_yellow_0(sK2,X0)) != k1_yellow_0(sK3,k9_relat_1(sK4,X0))
        | r4_waybel_0(sK2,sK3,sK4,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f450,f268])).

fof(f450,plain,
    ( ! [X0] :
        ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_yellow_0(sK2,X0)) != k1_yellow_0(sK3,k9_relat_1(sK4,X0))
        | ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
        | r4_waybel_0(sK2,sK3,sK5,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f449,f268])).

fof(f449,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
        | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,X0)) != k1_yellow_0(sK3,k9_relat_1(sK5,X0))
        | r4_waybel_0(sK2,sK3,sK5,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f448,f268])).

fof(f448,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK5,X0))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,X0)) != k1_yellow_0(sK3,k9_relat_1(sK5,X0))
      | r4_waybel_0(sK2,sK3,sK5,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f447,f59])).

fof(f447,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK5,X0))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,X0)) != k1_yellow_0(sK3,k9_relat_1(sK5,X0))
      | r4_waybel_0(sK2,sK3,sK5,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f446,f60])).

fof(f446,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK5,X0))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,X0)) != k1_yellow_0(sK3,k9_relat_1(sK5,X0))
      | r4_waybel_0(sK2,sK3,sK5,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f445,f61])).

fof(f445,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK5,X0))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,X0)) != k1_yellow_0(sK3,k9_relat_1(sK5,X0))
      | r4_waybel_0(sK2,sK3,sK5,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK3)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f444,f62])).

fof(f444,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK5,X0))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,X0)) != k1_yellow_0(sK3,k9_relat_1(sK5,X0))
      | r4_waybel_0(sK2,sK3,sK5,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f443,f68])).

fof(f443,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK5,X0))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,X0)) != k1_yellow_0(sK3,k9_relat_1(sK5,X0))
      | r4_waybel_0(sK2,sK3,sK5,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v1_funct_1(sK5)
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f442,f69])).

fof(f442,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK5,X0))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,X0)) != k1_yellow_0(sK3,k9_relat_1(sK5,X0))
      | r4_waybel_0(sK2,sK3,sK5,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK5)
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f440,f70])).

fof(f440,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK5,X0))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,X0)) != k1_yellow_0(sK3,k9_relat_1(sK5,X0))
      | r4_waybel_0(sK2,sK3,sK5,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK5)
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f93,f144])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3))
      | r4_waybel_0(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f667,plain,
    ( r1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f664,f64])).

fof(f664,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | r1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(resolution,[],[f660,f62])).

fof(f660,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(X1)
        | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        | r1_yellow_0(X1,k9_relat_1(sK4,sK6)) )
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f658,f58])).

fof(f658,plain,
    ( ! [X1] :
        ( r1_yellow_0(X1,k9_relat_1(sK4,sK6))
        | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        | ~ l1_orders_2(X1)
        | ~ l1_orders_2(sK1) )
    | ~ spl8_3
    | ~ spl8_24 ),
    inference(resolution,[],[f653,f81])).

% (25895)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (25893)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (25892)Refutation not found, incomplete strategy% (25892)------------------------------
% (25892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25892)Termination reason: Refutation not found, incomplete strategy

% (25892)Memory used [KB]: 11641
% (25892)Time elapsed: 0.092 s
% (25892)------------------------------
% (25892)------------------------------
% (25908)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (25897)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (25896)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% (25915)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f501,plain,
    ( spl8_1
    | ~ spl8_23 ),
    inference(avatar_contradiction_clause,[],[f500])).

fof(f500,plain,
    ( $false
    | spl8_1
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f499,f126])).

fof(f499,plain,
    ( r4_waybel_0(sK2,sK3,sK5,sK6)
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f498,f69])).

fof(f498,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | r4_waybel_0(sK2,sK3,sK5,sK6)
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f497,f68])).

fof(f497,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | r4_waybel_0(sK2,sK3,sK5,sK6)
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f496,f62])).

fof(f496,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | r4_waybel_0(sK2,sK3,sK5,sK6)
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f494,f61])).

fof(f494,plain,
    ( v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | r4_waybel_0(sK2,sK3,sK5,sK6)
    | ~ spl8_23 ),
    inference(resolution,[],[f241,f70])).

fof(f241,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
        | v2_struct_0(X2)
        | ~ l1_orders_2(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2))
        | r4_waybel_0(sK2,X2,X3,sK6) )
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl8_23
  <=> ! [X3,X2] :
        ( r4_waybel_0(sK2,X2,X3,sK6)
        | v2_struct_0(X2)
        | ~ l1_orders_2(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f485,plain,
    ( spl8_2
    | ~ spl8_19 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | spl8_2
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f483,f125])).

fof(f483,plain,
    ( r3_waybel_0(sK2,sK3,sK5,sK6)
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f482,f69])).

fof(f482,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | r3_waybel_0(sK2,sK3,sK5,sK6)
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f481,f68])).

fof(f481,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | r3_waybel_0(sK2,sK3,sK5,sK6)
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f480,f62])).

fof(f480,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | r3_waybel_0(sK2,sK3,sK5,sK6)
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f478,f61])).

fof(f478,plain,
    ( v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | r3_waybel_0(sK2,sK3,sK5,sK6)
    | ~ spl8_19 ),
    inference(resolution,[],[f219,f70])).

fof(f219,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
        | v2_struct_0(X2)
        | ~ l1_orders_2(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2))
        | r3_waybel_0(sK2,X2,X3,sK6) )
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl8_19
  <=> ! [X3,X2] :
        ( r3_waybel_0(sK2,X2,X3,sK6)
        | v2_struct_0(X2)
        | ~ l1_orders_2(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f306,plain,
    ( spl8_26
    | spl8_30 ),
    inference(avatar_split_clause,[],[f298,f304,f278])).

fof(f278,plain,
    ( spl8_26
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f298,plain,(
    ! [X2,X0,X1] :
      ( k3_funct_2(u1_struct_0(sK0),X0,X1,k2_yellow_0(sK0,X2)) = k1_funct_1(X1,k2_yellow_0(sK0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),X0)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f135,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f135,plain,(
    ! [X0] : m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f95,f56])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f302,plain,(
    ~ spl8_26 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f300,f55])).

fof(f300,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f299,f127])).

fof(f127,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f79,f56])).

fof(f79,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f299,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_26 ),
    inference(resolution,[],[f280,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f280,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f278])).

fof(f269,plain,
    ( spl8_15
    | spl8_25
    | spl8_13 ),
    inference(avatar_split_clause,[],[f264,f186,f266,f196])).

fof(f196,plain,
    ( spl8_15
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f186,plain,
    ( spl8_13
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f264,plain,
    ( sK4 = sK5
    | v1_xboole_0(u1_struct_0(sK3))
    | spl8_13 ),
    inference(subsumption_resolution,[],[f263,f187])).

fof(f187,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl8_13 ),
    inference(avatar_component_clause,[],[f186])).

fof(f263,plain,
    ( sK4 = sK5
    | v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f262,f65])).

fof(f262,plain,
    ( sK4 = sK5
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f261,f66])).

fof(f261,plain,
    ( sK4 = sK5
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f260,f67])).

fof(f260,plain,
    ( sK4 = sK5
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f259,f68])).

fof(f259,plain,
    ( sK4 = sK5
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f258,f69])).

fof(f258,plain,
    ( sK4 = sK5
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f247,f70])).

fof(f247,plain,
    ( sK4 = sK5
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f100,f71])).

fof(f71,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f257,plain,(
    ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f255,f61])).

fof(f255,plain,
    ( v2_struct_0(sK3)
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f254,f130])).

fof(f130,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f79,f62])).

fof(f254,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl8_15 ),
    inference(resolution,[],[f198,f85])).

fof(f198,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f196])).

fof(f253,plain,(
    ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f251,f57])).

fof(f251,plain,
    ( v2_struct_0(sK1)
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f250,f128])).

fof(f128,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f79,f58])).

fof(f250,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_13 ),
    inference(resolution,[],[f188,f85])).

fof(f188,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f186])).

fof(f246,plain,
    ( spl8_23
    | spl8_24 ),
    inference(avatar_split_clause,[],[f238,f243,f240])).

fof(f238,plain,(
    ! [X2,X3] :
      ( r1_yellow_0(sK2,sK6)
      | r4_waybel_0(sK2,X2,X3,sK6)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f237,f59])).

fof(f237,plain,(
    ! [X2,X3] :
      ( r1_yellow_0(sK2,sK6)
      | r4_waybel_0(sK2,X2,X3,sK6)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f226,f60])).

fof(f226,plain,(
    ! [X2,X3] :
      ( r1_yellow_0(sK2,sK6)
      | r4_waybel_0(sK2,X2,X3,sK6)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f92,f124])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_yellow_0(X0,X3)
      | r4_waybel_0(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f224,plain,
    ( spl8_19
    | spl8_20 ),
    inference(avatar_split_clause,[],[f216,f221,f218])).

fof(f216,plain,(
    ! [X2,X3] :
      ( r2_yellow_0(sK2,sK6)
      | r3_waybel_0(sK2,X2,X3,sK6)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f215,f59])).

fof(f215,plain,(
    ! [X2,X3] :
      ( r2_yellow_0(sK2,sK6)
      | r3_waybel_0(sK2,X2,X3,sK6)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f204,f60])).

fof(f204,plain,(
    ! [X2,X3] :
      ( r2_yellow_0(sK2,sK6)
      | r3_waybel_0(sK2,X2,X3,sK6)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f88,f124])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_yellow_0(X0,X3)
      | r3_waybel_0(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f123,plain,
    ( spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f75,f119,f114])).

fof(f75,plain,
    ( r3_waybel_0(sK0,sK1,sK4,sK6)
    | r4_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f122,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f76,f119,f105])).

fof(f76,plain,
    ( r3_waybel_0(sK0,sK1,sK4,sK6)
    | ~ r4_waybel_0(sK2,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f117,plain,
    ( spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f77,f109,f114])).

fof(f77,plain,
    ( ~ r3_waybel_0(sK2,sK3,sK5,sK7)
    | r4_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f112,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f78,f109,f105])).

fof(f78,plain,
    ( ~ r3_waybel_0(sK2,sK3,sK5,sK7)
    | ~ r4_waybel_0(sK2,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f49])).

%------------------------------------------------------------------------------
