%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t65_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:00 EDT 2019

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  583 (10139615 expanded)
%              Number of leaves         :   23 (5716026 expanded)
%              Depth                    :   84
%              Number of atoms          : 2981 (227085418 expanded)
%              Number of equality atoms :  556 (29701020 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6142,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6141,f5863])).

fof(f5863,plain,(
    k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f5862,f5563])).

fof(f5563,plain,
    ( r1_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(resolution,[],[f5559,f888])).

fof(f888,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK2,X0)
      | r1_yellow_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f883,f115])).

fof(f115,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f48,f99,f98,f97,f96,f95,f94,f93,f92])).

fof(f92,plain,
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
                  & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                  & l1_orders_2(X3)
                  & ~ v2_struct_0(X3) )
              & l1_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f93,plain,(
    ! [X0] :
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
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                                    & r3_waybel_0(X0,sK1,X4,X6) )
                                  | ( ~ r4_waybel_0(X2,X3,X5,X7)
                                    & r4_waybel_0(X0,sK1,X4,X6) ) )
                                & X6 = X7
                                & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                            & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                        & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                & l1_orders_2(X3)
                & ~ v2_struct_0(X3) )
            & l1_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & l1_orders_2(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
    ! [X0,X1] :
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
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ( ~ r3_waybel_0(sK2,X3,X5,X7)
                                & r3_waybel_0(X0,X1,X4,X6) )
                              | ( ~ r4_waybel_0(sK2,X3,X5,X7)
                                & r4_waybel_0(X0,X1,X4,X6) ) )
                            & X6 = X7
                            & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) )
                        & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                    & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK2),u1_struct_0(X3),X4,X5)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
                    & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X3))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
            & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
            & l1_orders_2(X3)
            & ~ v2_struct_0(X3) )
        & l1_orders_2(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
    ! [X2,X0,X1] :
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
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ( ~ r3_waybel_0(X2,sK3,X5,X7)
                            & r3_waybel_0(X0,X1,X4,X6) )
                          | ( ~ r4_waybel_0(X2,sK3,X5,X7)
                            & r4_waybel_0(X0,X1,X4,X6) ) )
                        & X6 = X7
                        & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                    & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(sK3),X4,X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK3))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
        & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        & l1_orders_2(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
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
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                        & r3_waybel_0(X0,X1,sK4,X6) )
                      | ( ~ r4_waybel_0(X2,X3,X5,X7)
                        & r4_waybel_0(X0,X1,sK4,X6) ) )
                    & X6 = X7
                    & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
            & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),sK4,X5)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
            & v1_funct_1(X5) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] :
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
     => ( ? [X6] :
            ( ? [X7] :
                ( ( ( ~ r3_waybel_0(X2,X3,sK5,X7)
                    & r3_waybel_0(X0,X1,X4,X6) )
                  | ( ~ r4_waybel_0(X2,X3,sK5,X7)
                    & r4_waybel_0(X0,X1,X4,X6) ) )
                & X6 = X7
                & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
            & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,sK5)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
        & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X3))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                  & r3_waybel_0(X0,X1,X4,X6) )
                | ( ~ r4_waybel_0(X2,X3,X5,X7)
                  & r4_waybel_0(X0,X1,X4,X6) ) )
              & X6 = X7
              & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X7] :
            ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                & r3_waybel_0(X0,X1,X4,sK6) )
              | ( ~ r4_waybel_0(X2,X3,X5,X7)
                & r4_waybel_0(X0,X1,X4,sK6) ) )
            & sK6 = X7
            & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
              & r3_waybel_0(X0,X1,X4,X6) )
            | ( ~ r4_waybel_0(X2,X3,X5,X7)
              & r4_waybel_0(X0,X1,X4,X6) ) )
          & X6 = X7
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ( ( ~ r3_waybel_0(X2,X3,X5,sK7)
            & r3_waybel_0(X0,X1,X4,X6) )
          | ( ~ r4_waybel_0(X2,X3,X5,sK7)
            & r4_waybel_0(X0,X1,X4,X6) ) )
        & sK7 = X6
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t65_waybel_0.p',t65_waybel_0)).

fof(f883,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK2,X0)
      | r1_yellow_0(sK0,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(equality_resolution,[],[f313])).

fof(f313,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | ~ r1_yellow_0(sK2,X1)
      | r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f301,f119])).

fof(f119,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f100])).

fof(f301,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | ~ r1_yellow_0(sK2,X1)
      | r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(sK2) ) ),
    inference(superposition,[],[f142,f122])).

fof(f122,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(cnf_transformation,[],[f100])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r1_yellow_0(X0,X2)
      | r1_yellow_0(X1,X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t65_waybel_0.p',t14_yellow_0)).

fof(f5559,plain,
    ( r1_yellow_0(sK2,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f5558,f131])).

fof(f131,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f100])).

fof(f5558,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r1_yellow_0(sK2,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f5557])).

fof(f5557,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r1_yellow_0(sK2,sK6)
    | r1_yellow_0(sK2,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f5545,f2048])).

fof(f2048,plain,(
    ! [X1] :
      ( r4_waybel_0(sK2,sK3,sK4,X1)
      | r1_yellow_0(sK2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f2047,f125])).

fof(f125,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f100])).

fof(f2047,plain,(
    ! [X1] :
      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_yellow_0(sK2,X1)
      | r4_waybel_0(sK2,sK3,sK4,X1) ) ),
    inference(forward_demodulation,[],[f2046,f691])).

fof(f691,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK3) ),
    inference(unit_resulting_resolution,[],[f123,f194,f165])).

fof(f165,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t65_waybel_0.p',free_g1_orders_2)).

fof(f194,plain,(
    m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f117,f140])).

fof(f140,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t65_waybel_0.p',dt_u1_orders_2)).

fof(f117,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f100])).

fof(f123,plain,(
    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f100])).

fof(f2046,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
      | r1_yellow_0(sK2,X1)
      | r4_waybel_0(sK2,sK3,sK4,X1) ) ),
    inference(subsumption_resolution,[],[f2045,f120])).

fof(f120,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f100])).

fof(f2045,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
      | r1_yellow_0(sK2,X1)
      | r4_waybel_0(sK2,sK3,sK4,X1)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f2044,f121])).

fof(f121,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f100])).

fof(f2044,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
      | r1_yellow_0(sK2,X1)
      | r4_waybel_0(sK2,sK3,sK4,X1)
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f2035,f126])).

fof(f126,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f100])).

fof(f2035,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
      | r1_yellow_0(sK2,X1)
      | r4_waybel_0(sK2,sK3,sK4,X1)
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(superposition,[],[f1146,f691])).

fof(f1146,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
      | r1_yellow_0(sK2,X1)
      | r4_waybel_0(sK2,X0,sK4,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f1145,f523])).

fof(f523,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f122,f189,f165])).

fof(f189,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f115,f140])).

fof(f1145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | r1_yellow_0(sK2,X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
      | r4_waybel_0(sK2,X0,sK4,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f1144,f523])).

fof(f1144,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_yellow_0(sK2,X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
      | r4_waybel_0(sK2,X0,sK4,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f1143,f118])).

fof(f118,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f100])).

fof(f1143,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_yellow_0(sK2,X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
      | r4_waybel_0(sK2,X0,sK4,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1134,f119])).

fof(f1134,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_yellow_0(sK2,X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
      | r4_waybel_0(sK2,X0,sK4,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f210,f523])).

fof(f210,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X8))))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | r1_yellow_0(X6,X7)
      | ~ v1_funct_2(sK4,u1_struct_0(X6),u1_struct_0(X8))
      | r4_waybel_0(X6,X8,sK4,X7)
      | ~ l1_orders_2(X8)
      | v2_struct_0(X8)
      | ~ l1_orders_2(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f124,f151])).

fof(f151,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | r1_yellow_0(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | r4_waybel_0(X0,X1,X2,X3)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r4_waybel_0(X0,X1,X2,X3)
                      | ( ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) != k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                          | ~ r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                        & r1_yellow_0(X0,X3) ) )
                    & ( ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) = k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
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
    inference(flattening,[],[f103])).

fof(f103,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r4_waybel_0(X0,X1,X2,X3)
                      | ( ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) != k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                          | ~ r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                        & r1_yellow_0(X0,X3) ) )
                    & ( ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) = k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
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
    inference(nnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r4_waybel_0(X0,X1,X2,X3)
                  <=> ( ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) = k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
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
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r4_waybel_0(X0,X1,X2,X3)
                  <=> ( ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) = k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
                     => ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) = k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                        & r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t65_waybel_0.p',d31_waybel_0)).

fof(f124,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f100])).

fof(f5545,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK4,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r1_yellow_0(sK2,sK6) ),
    inference(resolution,[],[f5288,f389])).

fof(f389,plain,
    ( ~ r3_waybel_0(sK2,sK3,sK4,sK6)
    | ~ r4_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(forward_demodulation,[],[f364,f356])).

fof(f356,plain,(
    sK4 = sK5 ),
    inference(unit_resulting_resolution,[],[f124,f127,f233,f236,f125,f128,f126,f129,f130,f177])).

fof(f177,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | X4 = X5
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
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
    inference(nnf_transformation,[],[f91])).

fof(f91,plain,(
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
    inference(flattening,[],[f90])).

fof(f90,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t65_waybel_0.p',redefinition_r1_funct_2)).

fof(f130,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f100])).

fof(f129,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f100])).

fof(f128,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f100])).

fof(f236,plain,(
    ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f120,f203,f148])).

fof(f148,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t65_waybel_0.p',fc2_struct_0)).

fof(f203,plain,(
    l1_struct_0(sK3) ),
    inference(unit_resulting_resolution,[],[f121,f139])).

fof(f139,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t65_waybel_0.p',dt_l1_orders_2)).

fof(f233,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f116,f193,f148])).

fof(f193,plain,(
    l1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f117,f139])).

fof(f116,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f100])).

fof(f127,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f100])).

fof(f364,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK4,sK6)
    | ~ r3_waybel_0(sK2,sK3,sK5,sK6) ),
    inference(backward_demodulation,[],[f356,f186])).

fof(f186,plain,
    ( ~ r3_waybel_0(sK2,sK3,sK5,sK6)
    | ~ r4_waybel_0(sK2,sK3,sK5,sK6) ),
    inference(forward_demodulation,[],[f185,f133])).

fof(f133,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f100])).

fof(f185,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK6)
    | ~ r3_waybel_0(sK2,sK3,sK5,sK7) ),
    inference(backward_demodulation,[],[f133,f137])).

fof(f137,plain,
    ( ~ r3_waybel_0(sK2,sK3,sK5,sK7)
    | ~ r4_waybel_0(sK2,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f100])).

fof(f5288,plain,
    ( r3_waybel_0(sK2,sK3,sK4,sK6)
    | r1_yellow_0(sK2,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f5267,f4765])).

fof(f4765,plain,
    ( r1_yellow_0(sK2,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f4764,f2491])).

fof(f2491,plain,
    ( r2_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(resolution,[],[f2304,f911])).

fof(f911,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f906,f115])).

fof(f906,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK0,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(equality_resolution,[],[f315])).

fof(f315,plain,(
    ! [X4,X5] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
      | ~ r2_yellow_0(sK2,X5)
      | r2_yellow_0(X4,X5)
      | ~ l1_orders_2(X4) ) ),
    inference(subsumption_resolution,[],[f303,f119])).

fof(f303,plain,(
    ! [X4,X5] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
      | ~ r2_yellow_0(sK2,X5)
      | r2_yellow_0(X4,X5)
      | ~ l1_orders_2(X4)
      | ~ l1_orders_2(sK2) ) ),
    inference(superposition,[],[f143,f122])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r2_yellow_0(X0,X2)
      | r2_yellow_0(X1,X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f2304,plain,
    ( r2_yellow_0(sK2,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(resolution,[],[f2281,f1109])).

fof(f1109,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK1,X0)
      | k1_yellow_0(sK1,X0) = k1_yellow_0(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f1104,f117])).

fof(f1104,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK1,X0)
      | k1_yellow_0(sK1,X0) = k1_yellow_0(sK3,X0)
      | ~ l1_orders_2(sK1) ) ),
    inference(equality_resolution,[],[f350])).

fof(f350,plain,(
    ! [X14,X15] :
      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X14),u1_orders_2(X14))
      | ~ r1_yellow_0(X14,X15)
      | k1_yellow_0(sK3,X15) = k1_yellow_0(X14,X15)
      | ~ l1_orders_2(X14) ) ),
    inference(subsumption_resolution,[],[f338,f121])).

fof(f338,plain,(
    ! [X14,X15] :
      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X14),u1_orders_2(X14))
      | ~ r1_yellow_0(X14,X15)
      | k1_yellow_0(sK3,X15) = k1_yellow_0(X14,X15)
      | ~ l1_orders_2(sK3)
      | ~ l1_orders_2(X14) ) ),
    inference(superposition,[],[f145,f123])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
              | ~ r1_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
              | ~ r1_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r1_yellow_0(X0,X2)
               => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t65_waybel_0.p',t26_yellow_0)).

fof(f2281,plain,
    ( r1_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | r2_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f2280,f2256])).

fof(f2256,plain,
    ( r1_yellow_0(sK0,sK6)
    | r2_yellow_0(sK2,sK6) ),
    inference(resolution,[],[f2254,f888])).

fof(f2254,plain,
    ( r1_yellow_0(sK2,sK6)
    | r2_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f2253,f131])).

fof(f2253,plain,
    ( r2_yellow_0(sK2,sK6)
    | r1_yellow_0(sK2,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f2222,f2048])).

fof(f2222,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK4,sK6)
    | r2_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f2220,f131])).

fof(f2220,plain,
    ( r2_yellow_0(sK2,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r4_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(resolution,[],[f2148,f389])).

fof(f2148,plain,(
    ! [X1] :
      ( r3_waybel_0(sK2,sK3,sK4,X1)
      | r2_yellow_0(sK2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f2147,f125])).

fof(f2147,plain,(
    ! [X1] :
      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_yellow_0(sK2,X1)
      | r3_waybel_0(sK2,sK3,sK4,X1) ) ),
    inference(forward_demodulation,[],[f2146,f691])).

fof(f2146,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
      | r2_yellow_0(sK2,X1)
      | r3_waybel_0(sK2,sK3,sK4,X1) ) ),
    inference(subsumption_resolution,[],[f2145,f120])).

fof(f2145,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
      | r2_yellow_0(sK2,X1)
      | r3_waybel_0(sK2,sK3,sK4,X1)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f2144,f121])).

fof(f2144,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
      | r2_yellow_0(sK2,X1)
      | r3_waybel_0(sK2,sK3,sK4,X1)
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f2135,f126])).

fof(f2135,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
      | r2_yellow_0(sK2,X1)
      | r3_waybel_0(sK2,sK3,sK4,X1)
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(superposition,[],[f1171,f691])).

fof(f1171,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
      | r2_yellow_0(sK2,X1)
      | r3_waybel_0(sK2,X0,sK4,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f1170,f523])).

fof(f1170,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | r2_yellow_0(sK2,X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
      | r3_waybel_0(sK2,X0,sK4,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f1169,f523])).

fof(f1169,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | r2_yellow_0(sK2,X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
      | r3_waybel_0(sK2,X0,sK4,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f1168,f118])).

fof(f1168,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | r2_yellow_0(sK2,X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
      | r3_waybel_0(sK2,X0,sK4,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1159,f119])).

fof(f1159,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | r2_yellow_0(sK2,X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
      | r3_waybel_0(sK2,X0,sK4,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f213,f523])).

fof(f213,plain,(
    ! [X17,X15,X16] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X17))))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | r2_yellow_0(X15,X16)
      | ~ v1_funct_2(sK4,u1_struct_0(X15),u1_struct_0(X17))
      | r3_waybel_0(X15,X17,sK4,X16)
      | ~ l1_orders_2(X17)
      | v2_struct_0(X17)
      | ~ l1_orders_2(X15)
      | v2_struct_0(X15) ) ),
    inference(resolution,[],[f124,f155])).

fof(f155,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | r2_yellow_0(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | r3_waybel_0(X0,X1,X2,X3)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
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
    inference(flattening,[],[f105])).

fof(f105,plain,(
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
    inference(nnf_transformation,[],[f66])).

fof(f66,plain,(
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
    inference(flattening,[],[f65])).

fof(f65,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t65_waybel_0.p',d30_waybel_0)).

fof(f2280,plain,
    ( r2_yellow_0(sK2,sK6)
    | r1_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f2277,f131])).

fof(f2277,plain,
    ( r2_yellow_0(sK2,sK6)
    | r1_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f2223,f1201])).

fof(f1201,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK0,sK1,sK4,X0)
      | r1_yellow_0(sK1,k9_relat_1(sK4,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0) ) ),
    inference(forward_demodulation,[],[f1200,f245])).

fof(f245,plain,(
    ! [X0] : k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(unit_resulting_resolution,[],[f126,f172])).

fof(f172,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t65_waybel_0.p',redefinition_k7_relset_1)).

fof(f1200,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) ) ),
    inference(subsumption_resolution,[],[f1199,f114])).

fof(f114,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f100])).

fof(f1199,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1198,f115])).

fof(f1198,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1197,f116])).

fof(f1197,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1196,f117])).

fof(f1196,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1191,f125])).

fof(f1191,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f208,f126])).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
      | ~ r4_waybel_0(X0,X2,sK4,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_yellow_0(X0,X1)
      | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X2))
      | r1_yellow_0(X2,k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),sK4,X1))
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f124,f149])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_yellow_0(X0,X3)
      | ~ r4_waybel_0(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f2223,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | r2_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f2221,f131])).

fof(f2221,plain,
    ( r2_yellow_0(sK2,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | r4_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(resolution,[],[f2148,f363])).

fof(f363,plain,
    ( ~ r3_waybel_0(sK2,sK3,sK4,sK6)
    | r4_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(backward_demodulation,[],[f356,f184])).

fof(f184,plain,
    ( ~ r3_waybel_0(sK2,sK3,sK5,sK6)
    | r4_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(backward_demodulation,[],[f133,f136])).

fof(f136,plain,
    ( ~ r3_waybel_0(sK2,sK3,sK5,sK7)
    | r4_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f100])).

fof(f4764,plain,
    ( r1_yellow_0(sK2,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f4762,f131])).

fof(f4762,plain,
    ( r1_yellow_0(sK2,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f4716,f2694])).

fof(f2694,plain,(
    ! [X0] :
      ( ~ r3_waybel_0(sK0,sK3,sK4,X0)
      | k2_yellow_0(sK3,k9_relat_1(sK4,X0)) = k1_funct_1(sK4,k2_yellow_0(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0) ) ),
    inference(forward_demodulation,[],[f2693,f245])).

fof(f2693,plain,(
    ! [X0] :
      ( k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) = k1_funct_1(sK4,k2_yellow_0(sK0,X0))
      | ~ r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0) ) ),
    inference(forward_demodulation,[],[f2692,f259])).

fof(f259,plain,(
    ! [X0] : k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0)) = k1_funct_1(sK4,k2_yellow_0(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f124,f232,f125,f126,f192,f174])).

fof(f174,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t65_waybel_0.p',redefinition_k3_funct_2)).

fof(f192,plain,(
    ! [X0] : m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f115,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t65_waybel_0.p',dt_k2_yellow_0)).

fof(f232,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f114,f188,f148])).

fof(f188,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f115,f139])).

fof(f2692,plain,(
    ! [X0] :
      ( k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0))
      | ~ r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f2691,f114])).

fof(f2691,plain,(
    ! [X0] :
      ( k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0))
      | ~ r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2690,f115])).

fof(f2690,plain,(
    ! [X0] :
      ( k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0))
      | ~ r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2685,f125])).

fof(f2685,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0))
      | ~ r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f1308,f126])).

fof(f1308,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK1))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK1),sK4,X3)) = k3_funct_2(u1_struct_0(X2),u1_struct_0(sK1),sK4,k2_yellow_0(X2,X3))
      | ~ r3_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_yellow_0(X2,X3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(forward_demodulation,[],[f1307,f691])).

fof(f1307,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ r3_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_yellow_0(X2,X3)
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,X3)) = k3_funct_2(u1_struct_0(X2),u1_struct_0(sK3),sK4,k2_yellow_0(X2,X3))
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(forward_demodulation,[],[f1306,f691])).

fof(f1306,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ r3_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_yellow_0(X2,X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK3))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,X3)) = k3_funct_2(u1_struct_0(X2),u1_struct_0(sK3),sK4,k2_yellow_0(X2,X3))
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1305,f120])).

fof(f1305,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ r3_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_yellow_0(X2,X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK3))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,X3)) = k3_funct_2(u1_struct_0(X2),u1_struct_0(sK3),sK4,k2_yellow_0(X2,X3))
      | v2_struct_0(sK3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1283,f121])).

fof(f1283,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ r3_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_yellow_0(X2,X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK3))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,X3)) = k3_funct_2(u1_struct_0(X2),u1_struct_0(sK3),sK4,k2_yellow_0(X2,X3))
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(superposition,[],[f212,f691])).

fof(f212,plain,(
    ! [X14,X12,X13] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X14))))
      | ~ r3_waybel_0(X12,X14,sK4,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ r2_yellow_0(X12,X13)
      | ~ v1_funct_2(sK4,u1_struct_0(X12),u1_struct_0(X14))
      | k2_yellow_0(X14,k7_relset_1(u1_struct_0(X12),u1_struct_0(X14),sK4,X13)) = k3_funct_2(u1_struct_0(X12),u1_struct_0(X14),sK4,k2_yellow_0(X12,X13))
      | ~ l1_orders_2(X14)
      | v2_struct_0(X14)
      | ~ l1_orders_2(X12)
      | v2_struct_0(X12) ) ),
    inference(resolution,[],[f124,f154])).

fof(f154,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_yellow_0(X0,X3)
      | ~ r3_waybel_0(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f4716,plain,
    ( r3_waybel_0(sK0,sK3,sK4,sK6)
    | r1_yellow_0(sK2,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f4715,f3314])).

fof(f3314,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f3313,f2491])).

fof(f3313,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f3310,f2656])).

fof(f2656,plain,
    ( r1_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f2193,f888])).

fof(f2193,plain,
    ( r1_yellow_0(sK2,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(resolution,[],[f2174,f1067])).

fof(f1067,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK1,X0)
      | k2_yellow_0(sK1,X0) = k2_yellow_0(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f1062,f117])).

fof(f1062,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK1,X0)
      | k2_yellow_0(sK1,X0) = k2_yellow_0(sK3,X0)
      | ~ l1_orders_2(sK1) ) ),
    inference(equality_resolution,[],[f348])).

fof(f348,plain,(
    ! [X10,X11] :
      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X10),u1_orders_2(X10))
      | ~ r2_yellow_0(X10,X11)
      | k2_yellow_0(sK3,X11) = k2_yellow_0(X10,X11)
      | ~ l1_orders_2(X10) ) ),
    inference(subsumption_resolution,[],[f336,f121])).

fof(f336,plain,(
    ! [X10,X11] :
      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X10),u1_orders_2(X10))
      | ~ r2_yellow_0(X10,X11)
      | k2_yellow_0(sK3,X11) = k2_yellow_0(X10,X11)
      | ~ l1_orders_2(sK3)
      | ~ l1_orders_2(X10) ) ),
    inference(superposition,[],[f144,f123])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
              | ~ r2_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
              | ~ r2_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r2_yellow_0(X0,X2)
               => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t65_waybel_0.p',t27_yellow_0)).

fof(f2174,plain,
    ( r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | r1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f2172,f131])).

fof(f2172,plain,
    ( r1_yellow_0(sK2,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_yellow_0(sK0,sK6)
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6)) ),
    inference(resolution,[],[f2048,f1352])).

fof(f1352,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK4,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f1348,f131])).

fof(f1348,plain,
    ( r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r4_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(resolution,[],[f1230,f362])).

fof(f362,plain,
    ( r3_waybel_0(sK0,sK1,sK4,sK6)
    | ~ r4_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(backward_demodulation,[],[f356,f183])).

fof(f183,plain,
    ( r3_waybel_0(sK0,sK1,sK4,sK6)
    | ~ r4_waybel_0(sK2,sK3,sK5,sK6) ),
    inference(backward_demodulation,[],[f133,f135])).

fof(f135,plain,
    ( r3_waybel_0(sK0,sK1,sK4,sK6)
    | ~ r4_waybel_0(sK2,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f100])).

fof(f1230,plain,(
    ! [X0] :
      ( ~ r3_waybel_0(sK0,sK1,sK4,X0)
      | r2_yellow_0(sK1,k9_relat_1(sK4,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0) ) ),
    inference(forward_demodulation,[],[f1229,f245])).

fof(f1229,plain,(
    ! [X0] :
      ( ~ r3_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) ) ),
    inference(subsumption_resolution,[],[f1228,f114])).

fof(f1228,plain,(
    ! [X0] :
      ( ~ r3_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1227,f115])).

fof(f1227,plain,(
    ! [X0] :
      ( ~ r3_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1226,f116])).

fof(f1226,plain,(
    ! [X0] :
      ( ~ r3_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1225,f117])).

fof(f1225,plain,(
    ! [X0] :
      ( ~ r3_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1220,f125])).

fof(f1220,plain,(
    ! [X0] :
      ( ~ r3_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f211,f126])).

fof(f211,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X11))))
      | ~ r3_waybel_0(X9,X11,sK4,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ r2_yellow_0(X9,X10)
      | ~ v1_funct_2(sK4,u1_struct_0(X9),u1_struct_0(X11))
      | r2_yellow_0(X11,k7_relset_1(u1_struct_0(X9),u1_struct_0(X11),sK4,X10))
      | ~ l1_orders_2(X11)
      | v2_struct_0(X11)
      | ~ l1_orders_2(X9)
      | v2_struct_0(X9) ) ),
    inference(resolution,[],[f124,f153])).

fof(f153,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_yellow_0(X0,X3)
      | ~ r3_waybel_0(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f3310,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(resolution,[],[f1405,f1067])).

fof(f1405,plain,
    ( r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(resolution,[],[f1355,f1109])).

fof(f1355,plain,
    ( r1_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f1354,f131])).

fof(f1354,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | r1_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f1353,f1201])).

fof(f1353,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f1349,f131])).

fof(f1349,plain,
    ( r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_yellow_0(sK0,sK6)
    | r4_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(resolution,[],[f1230,f134])).

fof(f134,plain,
    ( r3_waybel_0(sK0,sK1,sK4,sK6)
    | r4_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f100])).

fof(f4715,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r3_waybel_0(sK0,sK3,sK4,sK6)
    | r1_yellow_0(sK2,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f4713,f2491])).

fof(f4713,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r3_waybel_0(sK0,sK3,sK4,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | r1_yellow_0(sK2,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(superposition,[],[f4626,f4116])).

fof(f4116,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f4113,f2491])).

fof(f4113,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(duplicate_literal_removal,[],[f4111])).

fof(f4111,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f3108,f2633])).

fof(f2633,plain,
    ( r1_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f2173,f888])).

fof(f2173,plain,
    ( r1_yellow_0(sK2,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f2171,f131])).

fof(f2171,plain,
    ( r1_yellow_0(sK2,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(resolution,[],[f2048,f1370])).

fof(f1370,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK4,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f1366,f131])).

fof(f1366,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r4_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(resolution,[],[f1290,f362])).

fof(f1290,plain,(
    ! [X0] :
      ( ~ r3_waybel_0(sK0,sK1,sK4,X0)
      | k2_yellow_0(sK1,k9_relat_1(sK4,X0)) = k1_funct_1(sK4,k2_yellow_0(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0) ) ),
    inference(forward_demodulation,[],[f1289,f245])).

fof(f1289,plain,(
    ! [X0] :
      ( k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) = k1_funct_1(sK4,k2_yellow_0(sK0,X0))
      | ~ r3_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0) ) ),
    inference(forward_demodulation,[],[f1288,f259])).

fof(f1288,plain,(
    ! [X0] :
      ( ~ r3_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f1287,f114])).

fof(f1287,plain,(
    ! [X0] :
      ( ~ r3_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1286,f115])).

fof(f1286,plain,(
    ! [X0] :
      ( ~ r3_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1285,f116])).

fof(f1285,plain,(
    ! [X0] :
      ( ~ r3_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0))
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1284,f117])).

fof(f1284,plain,(
    ! [X0] :
      ( ~ r3_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1279,f125])).

fof(f1279,plain,(
    ! [X0] :
      ( ~ r3_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f212,f126])).

fof(f3108,plain,
    ( ~ r1_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f3106,f2491])).

fof(f3106,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(resolution,[],[f1997,f1109])).

fof(f1997,plain,
    ( r1_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f1995,f131])).

fof(f1995,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | r1_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f1371,f1201])).

fof(f1371,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f1367,f131])).

fof(f1367,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_yellow_0(sK0,sK6)
    | r4_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(resolution,[],[f1290,f134])).

fof(f4626,plain,
    ( k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | r3_waybel_0(sK0,sK3,sK4,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | r1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f4621,f131])).

fof(f4621,plain,
    ( r3_waybel_0(sK0,sK3,sK4,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | r1_yellow_0(sK2,sK6) ),
    inference(resolution,[],[f3565,f2174])).

fof(f3565,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK1,k9_relat_1(sK4,X0))
      | r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_yellow_0(sK3,k9_relat_1(sK4,X0)) != k1_funct_1(sK4,k2_yellow_0(sK0,X0)) ) ),
    inference(resolution,[],[f2995,f968])).

fof(f968,plain,(
    ! [X0] :
      ( r2_yellow_0(sK3,X0)
      | ~ r2_yellow_0(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f963,f117])).

fof(f963,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK1,X0)
      | r2_yellow_0(sK3,X0)
      | ~ l1_orders_2(sK1) ) ),
    inference(equality_resolution,[],[f346])).

fof(f346,plain,(
    ! [X6,X7] :
      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X6),u1_orders_2(X6))
      | ~ r2_yellow_0(X6,X7)
      | r2_yellow_0(sK3,X7)
      | ~ l1_orders_2(X6) ) ),
    inference(subsumption_resolution,[],[f334,f121])).

fof(f334,plain,(
    ! [X6,X7] :
      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X6),u1_orders_2(X6))
      | ~ r2_yellow_0(X6,X7)
      | r2_yellow_0(sK3,X7)
      | ~ l1_orders_2(sK3)
      | ~ l1_orders_2(X6) ) ),
    inference(superposition,[],[f143,f123])).

fof(f2995,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK4,X0))
      | k2_yellow_0(sK3,k9_relat_1(sK4,X0)) != k1_funct_1(sK4,k2_yellow_0(sK0,X0))
      | r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f2994,f245])).

fof(f2994,plain,(
    ! [X0] :
      ( k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k1_funct_1(sK4,k2_yellow_0(sK0,X0))
      | ~ r2_yellow_0(sK3,k9_relat_1(sK4,X0))
      | r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f2993,f259])).

fof(f2993,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK4,X0))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0))
      | r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f2992,f114])).

fof(f2992,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK4,X0))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0))
      | r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2991,f115])).

fof(f2991,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK4,X0))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0))
      | r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2990,f124])).

fof(f2990,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK4,X0))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0))
      | r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_1(sK4)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2989,f125])).

fof(f2989,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK4,X0))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0))
      | r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_1(sK4)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2965,f126])).

fof(f2965,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK4,X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,X0))
      | r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_1(sK4)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f798,f245])).

fof(f798,plain,(
    ! [X26,X27,X25] :
      ( ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(X25),u1_struct_0(sK1),X26,X27))
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(sK1))))
      | ~ v1_funct_2(X26,u1_struct_0(X25),u1_struct_0(sK1))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(X25),u1_struct_0(sK1),X26,X27)) != k3_funct_2(u1_struct_0(X25),u1_struct_0(sK1),X26,k2_yellow_0(X25,X27))
      | r3_waybel_0(X25,sK3,X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ v1_funct_1(X26)
      | ~ l1_orders_2(X25)
      | v2_struct_0(X25) ) ),
    inference(forward_demodulation,[],[f797,f691])).

fof(f797,plain,(
    ! [X26,X27,X25] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(sK1))))
      | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(X25),u1_struct_0(sK1),X26,X27))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(X25),u1_struct_0(sK1),X26,X27)) != k3_funct_2(u1_struct_0(X25),u1_struct_0(sK1),X26,k2_yellow_0(X25,X27))
      | r3_waybel_0(X25,sK3,X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ v1_funct_2(X26,u1_struct_0(X25),u1_struct_0(sK3))
      | ~ v1_funct_1(X26)
      | ~ l1_orders_2(X25)
      | v2_struct_0(X25) ) ),
    inference(forward_demodulation,[],[f796,f691])).

fof(f796,plain,(
    ! [X26,X27,X25] :
      ( ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(X25),u1_struct_0(sK1),X26,X27))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(X25),u1_struct_0(sK1),X26,X27)) != k3_funct_2(u1_struct_0(X25),u1_struct_0(sK1),X26,k2_yellow_0(X25,X27))
      | r3_waybel_0(X25,sK3,X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(sK3))))
      | ~ v1_funct_2(X26,u1_struct_0(X25),u1_struct_0(sK3))
      | ~ v1_funct_1(X26)
      | ~ l1_orders_2(X25)
      | v2_struct_0(X25) ) ),
    inference(forward_demodulation,[],[f795,f691])).

fof(f795,plain,(
    ! [X26,X27,X25] :
      ( k2_yellow_0(sK3,k7_relset_1(u1_struct_0(X25),u1_struct_0(sK1),X26,X27)) != k3_funct_2(u1_struct_0(X25),u1_struct_0(sK1),X26,k2_yellow_0(X25,X27))
      | r3_waybel_0(X25,sK3,X26,X27)
      | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(X25),u1_struct_0(sK3),X26,X27))
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(sK3))))
      | ~ v1_funct_2(X26,u1_struct_0(X25),u1_struct_0(sK3))
      | ~ v1_funct_1(X26)
      | ~ l1_orders_2(X25)
      | v2_struct_0(X25) ) ),
    inference(subsumption_resolution,[],[f794,f120])).

fof(f794,plain,(
    ! [X26,X27,X25] :
      ( k2_yellow_0(sK3,k7_relset_1(u1_struct_0(X25),u1_struct_0(sK1),X26,X27)) != k3_funct_2(u1_struct_0(X25),u1_struct_0(sK1),X26,k2_yellow_0(X25,X27))
      | r3_waybel_0(X25,sK3,X26,X27)
      | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(X25),u1_struct_0(sK3),X26,X27))
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(sK3))))
      | ~ v1_funct_2(X26,u1_struct_0(X25),u1_struct_0(sK3))
      | ~ v1_funct_1(X26)
      | v2_struct_0(sK3)
      | ~ l1_orders_2(X25)
      | v2_struct_0(X25) ) ),
    inference(subsumption_resolution,[],[f756,f121])).

fof(f756,plain,(
    ! [X26,X27,X25] :
      ( k2_yellow_0(sK3,k7_relset_1(u1_struct_0(X25),u1_struct_0(sK1),X26,X27)) != k3_funct_2(u1_struct_0(X25),u1_struct_0(sK1),X26,k2_yellow_0(X25,X27))
      | r3_waybel_0(X25,sK3,X26,X27)
      | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(X25),u1_struct_0(sK3),X26,X27))
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(sK3))))
      | ~ v1_funct_2(X26,u1_struct_0(X25),u1_struct_0(sK3))
      | ~ v1_funct_1(X26)
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ l1_orders_2(X25)
      | v2_struct_0(X25) ) ),
    inference(superposition,[],[f156,f691])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
      | r3_waybel_0(X0,X1,X2,X3)
      | ~ r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f5267,plain,
    ( k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r1_yellow_0(sK2,sK6)
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(backward_demodulation,[],[f5177,f4776])).

fof(f4776,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r1_yellow_0(sK2,sK6)
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK2,sK6))
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(subsumption_resolution,[],[f4770,f131])).

fof(f4770,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r1_yellow_0(sK2,sK6)
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK2,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(resolution,[],[f4767,f4313])).

fof(f4313,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK4,X0))
      | k2_yellow_0(sK3,k9_relat_1(sK4,X0)) != k1_funct_1(sK4,k2_yellow_0(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r3_waybel_0(sK2,sK3,sK4,X0) ) ),
    inference(forward_demodulation,[],[f4312,f245])).

fof(f4312,plain,(
    ! [X0] :
      ( k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k1_funct_1(sK4,k2_yellow_0(sK2,X0))
      | ~ r2_yellow_0(sK3,k9_relat_1(sK4,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r3_waybel_0(sK2,sK3,sK4,X0) ) ),
    inference(forward_demodulation,[],[f4311,f682])).

fof(f682,plain,(
    ! [X0] : k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK2,X0)) = k1_funct_1(sK4,k2_yellow_0(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f124,f232,f125,f126,f541,f174])).

fof(f541,plain,(
    ! [X0] : m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f523,f202])).

fof(f202,plain,(
    ! [X0] : m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f119,f159])).

fof(f4311,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK4,X0))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r3_waybel_0(sK2,sK3,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f4310,f124])).

fof(f4310,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK4,X0))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r3_waybel_0(sK2,sK3,sK4,X0)
      | ~ v1_funct_1(sK4) ) ),
    inference(subsumption_resolution,[],[f4309,f126])).

fof(f4309,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK4,X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r3_waybel_0(sK2,sK3,sK4,X0)
      | ~ v1_funct_1(sK4) ) ),
    inference(subsumption_resolution,[],[f4308,f125])).

fof(f4308,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK3,k9_relat_1(sK4,X0))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r3_waybel_0(sK2,sK3,sK4,X0)
      | ~ v1_funct_1(sK4) ) ),
    inference(superposition,[],[f2806,f245])).

fof(f2806,plain,(
    ! [X2,X3] :
      ( ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_yellow_0(sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r3_waybel_0(sK2,sK3,X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f2805,f691])).

fof(f2805,plain,(
    ! [X2,X3] :
      ( ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_yellow_0(sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK3))
      | r3_waybel_0(sK2,sK3,X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f2804,f691])).

fof(f2804,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_yellow_0(sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK3))
      | r3_waybel_0(sK2,sK3,X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f2803,f691])).

fof(f2803,plain,(
    ! [X2,X3] :
      ( k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_yellow_0(sK2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK3))
      | r3_waybel_0(sK2,sK3,X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f2802,f120])).

fof(f2802,plain,(
    ! [X2,X3] :
      ( k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_yellow_0(sK2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK3))
      | r3_waybel_0(sK2,sK3,X2,X3)
      | ~ v1_funct_1(X2)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f2793,f121])).

fof(f2793,plain,(
    ! [X2,X3] :
      ( k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_yellow_0(sK2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK3))
      | r3_waybel_0(sK2,sK3,X2,X3)
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(superposition,[],[f619,f691])).

fof(f619,plain,(
    ! [X24,X23,X22] :
      ( k2_yellow_0(X22,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X24)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(X22),X23,k2_yellow_0(sK2,X24))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22))))
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(X22,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X24))
      | ~ v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22))
      | r3_waybel_0(sK2,X22,X23,X24)
      | ~ v1_funct_1(X23)
      | ~ l1_orders_2(X22)
      | v2_struct_0(X22) ) ),
    inference(forward_demodulation,[],[f618,f523])).

fof(f618,plain,(
    ! [X24,X23,X22] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22))))
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(X22,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X24))
      | k2_yellow_0(X22,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X24)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(X22),X23,k2_yellow_0(sK2,X24))
      | r3_waybel_0(sK2,X22,X23,X24)
      | ~ v1_funct_2(X23,u1_struct_0(sK2),u1_struct_0(X22))
      | ~ v1_funct_1(X23)
      | ~ l1_orders_2(X22)
      | v2_struct_0(X22) ) ),
    inference(forward_demodulation,[],[f617,f523])).

fof(f617,plain,(
    ! [X24,X23,X22] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(X22,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X24))
      | k2_yellow_0(X22,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X24)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(X22),X23,k2_yellow_0(sK2,X24))
      | r3_waybel_0(sK2,X22,X23,X24)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X22))))
      | ~ v1_funct_2(X23,u1_struct_0(sK2),u1_struct_0(X22))
      | ~ v1_funct_1(X23)
      | ~ l1_orders_2(X22)
      | v2_struct_0(X22) ) ),
    inference(forward_demodulation,[],[f616,f523])).

fof(f616,plain,(
    ! [X24,X23,X22] :
      ( ~ r2_yellow_0(X22,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X24))
      | k2_yellow_0(X22,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X24)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(X22),X23,k2_yellow_0(sK2,X24))
      | r3_waybel_0(sK2,X22,X23,X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X22))))
      | ~ v1_funct_2(X23,u1_struct_0(sK2),u1_struct_0(X22))
      | ~ v1_funct_1(X23)
      | ~ l1_orders_2(X22)
      | v2_struct_0(X22) ) ),
    inference(forward_demodulation,[],[f615,f523])).

fof(f615,plain,(
    ! [X24,X23,X22] :
      ( k2_yellow_0(X22,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X24)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(X22),X23,k2_yellow_0(sK2,X24))
      | r3_waybel_0(sK2,X22,X23,X24)
      | ~ r2_yellow_0(X22,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X22),X23,X24))
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X22))))
      | ~ v1_funct_2(X23,u1_struct_0(sK2),u1_struct_0(X22))
      | ~ v1_funct_1(X23)
      | ~ l1_orders_2(X22)
      | v2_struct_0(X22) ) ),
    inference(subsumption_resolution,[],[f614,f118])).

fof(f614,plain,(
    ! [X24,X23,X22] :
      ( k2_yellow_0(X22,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X24)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(X22),X23,k2_yellow_0(sK2,X24))
      | r3_waybel_0(sK2,X22,X23,X24)
      | ~ r2_yellow_0(X22,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X22),X23,X24))
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X22))))
      | ~ v1_funct_2(X23,u1_struct_0(sK2),u1_struct_0(X22))
      | ~ v1_funct_1(X23)
      | ~ l1_orders_2(X22)
      | v2_struct_0(X22)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f581,f119])).

fof(f581,plain,(
    ! [X24,X23,X22] :
      ( k2_yellow_0(X22,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X24)) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(X22),X23,k2_yellow_0(sK2,X24))
      | r3_waybel_0(sK2,X22,X23,X24)
      | ~ r2_yellow_0(X22,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X22),X23,X24))
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X22))))
      | ~ v1_funct_2(X23,u1_struct_0(sK2),u1_struct_0(X22))
      | ~ v1_funct_1(X23)
      | ~ l1_orders_2(X22)
      | v2_struct_0(X22)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f156,f523])).

fof(f4767,plain,
    ( r2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f4766,f2491])).

fof(f4766,plain,
    ( r1_yellow_0(sK2,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f4763,f131])).

fof(f4763,plain,
    ( r1_yellow_0(sK2,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f4716,f2426])).

fof(f2426,plain,(
    ! [X0] :
      ( ~ r3_waybel_0(sK0,sK3,sK4,X0)
      | r2_yellow_0(sK3,k9_relat_1(sK4,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0) ) ),
    inference(forward_demodulation,[],[f2425,f245])).

fof(f2425,plain,(
    ! [X0] :
      ( r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f2424,f114])).

fof(f2424,plain,(
    ! [X0] :
      ( r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2423,f115])).

fof(f2423,plain,(
    ! [X0] :
      ( r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2418,f125])).

fof(f2418,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ r3_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_yellow_0(sK0,X0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f1248,f126])).

fof(f1248,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK1))
      | r2_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK1),sK4,X3))
      | ~ r3_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_yellow_0(X2,X3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(forward_demodulation,[],[f1247,f691])).

fof(f1247,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ r3_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_yellow_0(X2,X3)
      | r2_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,X3))
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(forward_demodulation,[],[f1246,f691])).

fof(f1246,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ r3_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_yellow_0(X2,X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK3))
      | r2_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,X3))
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1245,f120])).

fof(f1245,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ r3_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_yellow_0(X2,X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK3))
      | r2_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,X3))
      | v2_struct_0(sK3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1224,f121])).

fof(f1224,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ r3_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_yellow_0(X2,X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK3))
      | r2_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,X3))
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(superposition,[],[f211,f691])).

fof(f5177,plain,(
    k2_yellow_0(sK0,sK6) = k2_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f5176,f4681])).

fof(f4681,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | k2_yellow_0(sK0,sK6) = k2_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f4680,f995])).

fof(f995,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK2,X0)
      | k2_yellow_0(sK0,X0) = k2_yellow_0(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f990,f115])).

fof(f990,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK2,X0)
      | k2_yellow_0(sK0,X0) = k2_yellow_0(sK2,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(equality_resolution,[],[f317])).

fof(f317,plain,(
    ! [X8,X9] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X8),u1_orders_2(X8))
      | ~ r2_yellow_0(sK2,X9)
      | k2_yellow_0(sK2,X9) = k2_yellow_0(X8,X9)
      | ~ l1_orders_2(X8) ) ),
    inference(subsumption_resolution,[],[f305,f119])).

fof(f305,plain,(
    ! [X8,X9] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X8),u1_orders_2(X8))
      | ~ r2_yellow_0(sK2,X9)
      | k2_yellow_0(sK2,X9) = k2_yellow_0(X8,X9)
      | ~ l1_orders_2(X8)
      | ~ l1_orders_2(sK2) ) ),
    inference(superposition,[],[f144,f122])).

fof(f4680,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | k2_yellow_0(sK0,sK6) = k2_yellow_0(sK2,sK6)
    | r2_yellow_0(sK2,sK6) ),
    inference(resolution,[],[f4617,f2256])).

fof(f4617,plain,
    ( ~ r1_yellow_0(sK0,sK6)
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | k2_yellow_0(sK0,sK6) = k2_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f4615,f131])).

fof(f4615,plain,
    ( k2_yellow_0(sK0,sK6) = k2_yellow_0(sK2,sK6)
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f4614,f2569])).

fof(f2569,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK0,sK3,sK4,X0)
      | k1_yellow_0(sK3,k9_relat_1(sK4,X0)) = k1_funct_1(sK4,k1_yellow_0(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0) ) ),
    inference(forward_demodulation,[],[f2568,f248])).

fof(f248,plain,(
    ! [X0] : k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) = k1_funct_1(sK4,k1_yellow_0(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f124,f232,f191,f125,f126,f174])).

fof(f191,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f115,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t65_waybel_0.p',dt_k1_yellow_0)).

fof(f2568,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) = k1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | ~ r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0) ) ),
    inference(forward_demodulation,[],[f2567,f245])).

fof(f2567,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) = k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f2566,f114])).

fof(f2566,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) = k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2565,f115])).

fof(f2565,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) = k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2560,f125])).

fof(f2560,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) = k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f1278,f126])).

fof(f1278,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(X2),u1_struct_0(sK1),sK4,k1_yellow_0(X2,X3)) = k1_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK1),sK4,X3))
      | ~ r4_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_yellow_0(X2,X3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(forward_demodulation,[],[f1277,f691])).

fof(f1277,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ r4_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_yellow_0(X2,X3)
      | k3_funct_2(u1_struct_0(X2),u1_struct_0(sK3),sK4,k1_yellow_0(X2,X3)) = k1_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,X3))
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(forward_demodulation,[],[f1276,f691])).

fof(f1276,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ r4_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_yellow_0(X2,X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK3))
      | k3_funct_2(u1_struct_0(X2),u1_struct_0(sK3),sK4,k1_yellow_0(X2,X3)) = k1_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,X3))
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1275,f120])).

fof(f1275,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ r4_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_yellow_0(X2,X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK3))
      | k3_funct_2(u1_struct_0(X2),u1_struct_0(sK3),sK4,k1_yellow_0(X2,X3)) = k1_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,X3))
      | v2_struct_0(sK3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1253,f121])).

fof(f1253,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ r4_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_yellow_0(X2,X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK3))
      | k3_funct_2(u1_struct_0(X2),u1_struct_0(sK3),sK4,k1_yellow_0(X2,X3)) = k1_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,X3))
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(superposition,[],[f209,f691])).

fof(f209,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X5))))
      | ~ r4_waybel_0(X3,X5,sK4,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ r1_yellow_0(X3,X4)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X5))
      | k3_funct_2(u1_struct_0(X3),u1_struct_0(X5),sK4,k1_yellow_0(X3,X4)) = k1_yellow_0(X5,k7_relset_1(u1_struct_0(X3),u1_struct_0(X5),sK4,X4))
      | ~ l1_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_orders_2(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f124,f150])).

fof(f150,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_yellow_0(X0,X3)
      | ~ r4_waybel_0(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) = k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f4614,plain,
    ( r4_waybel_0(sK0,sK3,sK4,sK6)
    | k2_yellow_0(sK0,sK6) = k2_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f4613,f2490])).

fof(f2490,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k2_yellow_0(sK0,sK6) = k2_yellow_0(sK2,sK6) ),
    inference(resolution,[],[f2304,f995])).

fof(f4613,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r4_waybel_0(sK0,sK3,sK4,sK6)
    | k2_yellow_0(sK0,sK6) = k2_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f4610,f995])).

fof(f4610,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r4_waybel_0(sK0,sK3,sK4,sK6)
    | r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK0,sK6) = k2_yellow_0(sK2,sK6) ),
    inference(superposition,[],[f4606,f2487])).

fof(f2487,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | k2_yellow_0(sK0,sK6) = k2_yellow_0(sK2,sK6) ),
    inference(resolution,[],[f2279,f995])).

fof(f2279,plain,
    ( r2_yellow_0(sK2,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f2278,f2256])).

fof(f2278,plain,
    ( r2_yellow_0(sK2,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f2276,f131])).

fof(f2276,plain,
    ( r2_yellow_0(sK2,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f2223,f1260])).

fof(f1260,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK0,sK1,sK4,X0)
      | k1_yellow_0(sK1,k9_relat_1(sK4,X0)) = k1_funct_1(sK4,k1_yellow_0(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0) ) ),
    inference(forward_demodulation,[],[f1259,f248])).

fof(f1259,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) = k1_yellow_0(sK1,k9_relat_1(sK4,X0))
      | ~ r4_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0) ) ),
    inference(forward_demodulation,[],[f1258,f245])).

fof(f1258,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) = k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) ) ),
    inference(subsumption_resolution,[],[f1257,f114])).

fof(f1257,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) = k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1256,f115])).

fof(f1256,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) = k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1255,f116])).

fof(f1255,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) = k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1254,f117])).

fof(f1254,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) = k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1249,f125])).

fof(f1249,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK0,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) = k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f209,f126])).

fof(f4606,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | r4_waybel_0(sK0,sK3,sK4,sK6)
    | r2_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f4601,f131])).

fof(f4601,plain,
    ( r4_waybel_0(sK0,sK3,sK4,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | r2_yellow_0(sK2,sK6) ),
    inference(resolution,[],[f3556,f2281])).

fof(f3556,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK1,k9_relat_1(sK4,X0))
      | r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_yellow_0(sK3,k9_relat_1(sK4,X0)) != k1_funct_1(sK4,k1_yellow_0(sK0,X0)) ) ),
    inference(resolution,[],[f2927,f945])).

fof(f945,plain,(
    ! [X0] :
      ( r1_yellow_0(sK3,X0)
      | ~ r1_yellow_0(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f940,f117])).

fof(f940,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK1,X0)
      | r1_yellow_0(sK3,X0)
      | ~ l1_orders_2(sK1) ) ),
    inference(equality_resolution,[],[f344])).

fof(f344,plain,(
    ! [X2,X3] :
      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
      | ~ r1_yellow_0(X2,X3)
      | r1_yellow_0(sK3,X3)
      | ~ l1_orders_2(X2) ) ),
    inference(subsumption_resolution,[],[f332,f121])).

fof(f332,plain,(
    ! [X2,X3] :
      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
      | ~ r1_yellow_0(X2,X3)
      | r1_yellow_0(sK3,X3)
      | ~ l1_orders_2(sK3)
      | ~ l1_orders_2(X2) ) ),
    inference(superposition,[],[f142,f123])).

fof(f2927,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | k1_yellow_0(sK3,k9_relat_1(sK4,X0)) != k1_funct_1(sK4,k1_yellow_0(sK0,X0))
      | r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f2926,f248])).

fof(f2926,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) != k1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f2925,f245])).

fof(f2925,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f2924,f114])).

fof(f2924,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2923,f115])).

fof(f2923,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2922,f124])).

fof(f2922,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_1(sK4)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2921,f125])).

fof(f2921,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_1(sK4)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2897,f126])).

fof(f2897,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,X0)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_1(sK4)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f787,f245])).

fof(f787,plain,(
    ! [X21,X19,X20] :
      ( ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(X19),u1_struct_0(sK1),X20,X21))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(sK1))))
      | ~ v1_funct_2(X20,u1_struct_0(X19),u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(X19),u1_struct_0(sK1),X20,k1_yellow_0(X19,X21)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(X19),u1_struct_0(sK1),X20,X21))
      | r4_waybel_0(X19,sK3,X20,X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ v1_funct_1(X20)
      | ~ l1_orders_2(X19)
      | v2_struct_0(X19) ) ),
    inference(forward_demodulation,[],[f786,f691])).

fof(f786,plain,(
    ! [X21,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(sK1))))
      | ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(X19),u1_struct_0(sK1),X20,X21))
      | k3_funct_2(u1_struct_0(X19),u1_struct_0(sK1),X20,k1_yellow_0(X19,X21)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(X19),u1_struct_0(sK1),X20,X21))
      | r4_waybel_0(X19,sK3,X20,X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ v1_funct_2(X20,u1_struct_0(X19),u1_struct_0(sK3))
      | ~ v1_funct_1(X20)
      | ~ l1_orders_2(X19)
      | v2_struct_0(X19) ) ),
    inference(forward_demodulation,[],[f785,f691])).

fof(f785,plain,(
    ! [X21,X19,X20] :
      ( ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(X19),u1_struct_0(sK1),X20,X21))
      | k3_funct_2(u1_struct_0(X19),u1_struct_0(sK1),X20,k1_yellow_0(X19,X21)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(X19),u1_struct_0(sK1),X20,X21))
      | r4_waybel_0(X19,sK3,X20,X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(sK3))))
      | ~ v1_funct_2(X20,u1_struct_0(X19),u1_struct_0(sK3))
      | ~ v1_funct_1(X20)
      | ~ l1_orders_2(X19)
      | v2_struct_0(X19) ) ),
    inference(forward_demodulation,[],[f784,f691])).

fof(f784,plain,(
    ! [X21,X19,X20] :
      ( k3_funct_2(u1_struct_0(X19),u1_struct_0(sK1),X20,k1_yellow_0(X19,X21)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(X19),u1_struct_0(sK1),X20,X21))
      | r4_waybel_0(X19,sK3,X20,X21)
      | ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(X19),u1_struct_0(sK3),X20,X21))
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(sK3))))
      | ~ v1_funct_2(X20,u1_struct_0(X19),u1_struct_0(sK3))
      | ~ v1_funct_1(X20)
      | ~ l1_orders_2(X19)
      | v2_struct_0(X19) ) ),
    inference(subsumption_resolution,[],[f783,f120])).

fof(f783,plain,(
    ! [X21,X19,X20] :
      ( k3_funct_2(u1_struct_0(X19),u1_struct_0(sK1),X20,k1_yellow_0(X19,X21)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(X19),u1_struct_0(sK1),X20,X21))
      | r4_waybel_0(X19,sK3,X20,X21)
      | ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(X19),u1_struct_0(sK3),X20,X21))
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(sK3))))
      | ~ v1_funct_2(X20,u1_struct_0(X19),u1_struct_0(sK3))
      | ~ v1_funct_1(X20)
      | v2_struct_0(sK3)
      | ~ l1_orders_2(X19)
      | v2_struct_0(X19) ) ),
    inference(subsumption_resolution,[],[f754,f121])).

fof(f754,plain,(
    ! [X21,X19,X20] :
      ( k3_funct_2(u1_struct_0(X19),u1_struct_0(sK1),X20,k1_yellow_0(X19,X21)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(X19),u1_struct_0(sK1),X20,X21))
      | r4_waybel_0(X19,sK3,X20,X21)
      | ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(X19),u1_struct_0(sK3),X20,X21))
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(sK3))))
      | ~ v1_funct_2(X20,u1_struct_0(X19),u1_struct_0(sK3))
      | ~ v1_funct_1(X20)
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ l1_orders_2(X19)
      | v2_struct_0(X19) ) ),
    inference(superposition,[],[f152,f691])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) != k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | r4_waybel_0(X0,X1,X2,X3)
      | ~ r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f5176,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | k2_yellow_0(sK0,sK6) = k2_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f5174,f995])).

fof(f5174,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK0,sK6) = k2_yellow_0(sK2,sK6) ),
    inference(superposition,[],[f5171,f2305])).

fof(f2305,plain,
    ( k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6)
    | k2_yellow_0(sK0,sK6) = k2_yellow_0(sK2,sK6) ),
    inference(resolution,[],[f2255,f995])).

fof(f2255,plain,
    ( r2_yellow_0(sK2,sK6)
    | k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6) ),
    inference(resolution,[],[f2254,f1019])).

fof(f1019,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK2,X0)
      | k1_yellow_0(sK0,X0) = k1_yellow_0(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f1014,f115])).

fof(f1014,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK2,X0)
      | k1_yellow_0(sK0,X0) = k1_yellow_0(sK2,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(equality_resolution,[],[f319])).

fof(f319,plain,(
    ! [X12,X13] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X12),u1_orders_2(X12))
      | ~ r1_yellow_0(sK2,X13)
      | k1_yellow_0(sK2,X13) = k1_yellow_0(X12,X13)
      | ~ l1_orders_2(X12) ) ),
    inference(subsumption_resolution,[],[f307,f119])).

fof(f307,plain,(
    ! [X12,X13] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X12),u1_orders_2(X12))
      | ~ r1_yellow_0(sK2,X13)
      | k1_yellow_0(sK2,X13) = k1_yellow_0(X12,X13)
      | ~ l1_orders_2(X12)
      | ~ l1_orders_2(sK2) ) ),
    inference(superposition,[],[f145,f122])).

fof(f5171,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | r2_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f5170,f2222])).

fof(f5170,plain,
    ( r4_waybel_0(sK2,sK3,sK4,sK6)
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | r2_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f5164,f131])).

fof(f5164,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | r4_waybel_0(sK2,sK3,sK4,sK6)
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | r2_yellow_0(sK2,sK6) ),
    inference(resolution,[],[f4641,f2281])).

fof(f4641,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK1,k9_relat_1(sK4,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r4_waybel_0(sK2,sK3,sK4,X0)
      | k1_yellow_0(sK3,k9_relat_1(sK4,X0)) != k1_funct_1(sK4,k1_yellow_0(sK2,X0)) ) ),
    inference(resolution,[],[f4229,f945])).

fof(f4229,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | k1_yellow_0(sK3,k9_relat_1(sK4,X0)) != k1_funct_1(sK4,k1_yellow_0(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r4_waybel_0(sK2,sK3,sK4,X0) ) ),
    inference(forward_demodulation,[],[f4228,f653])).

fof(f653,plain,(
    ! [X0] : k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK2,X0)) = k1_funct_1(sK4,k1_yellow_0(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f124,f232,f125,f126,f540,f174])).

fof(f540,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f523,f201])).

fof(f201,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f119,f158])).

fof(f4228,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK2,X0)) != k1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r4_waybel_0(sK2,sK3,sK4,X0) ) ),
    inference(forward_demodulation,[],[f4227,f245])).

fof(f4227,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK2,X0)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r4_waybel_0(sK2,sK3,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f4226,f124])).

fof(f4226,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK2,X0)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r4_waybel_0(sK2,sK3,sK4,X0)
      | ~ v1_funct_1(sK4) ) ),
    inference(subsumption_resolution,[],[f4225,f126])).

fof(f4225,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK2,X0)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r4_waybel_0(sK2,sK3,sK4,X0)
      | ~ v1_funct_1(sK4) ) ),
    inference(subsumption_resolution,[],[f4224,f125])).

fof(f4224,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK2,X0)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r4_waybel_0(sK2,sK3,sK4,X0)
      | ~ v1_funct_1(sK4) ) ),
    inference(superposition,[],[f2745,f245])).

fof(f2745,plain,(
    ! [X2,X3] :
      ( ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,k1_yellow_0(sK2,X3)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r4_waybel_0(sK2,sK3,X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f2744,f691])).

fof(f2744,plain,(
    ! [X2,X3] :
      ( ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,k1_yellow_0(sK2,X3)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK3))
      | r4_waybel_0(sK2,sK3,X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f2743,f691])).

fof(f2743,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,k1_yellow_0(sK2,X3)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK3))
      | r4_waybel_0(sK2,sK3,X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f2742,f691])).

fof(f2742,plain,(
    ! [X2,X3] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,k1_yellow_0(sK2,X3)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK3))
      | r4_waybel_0(sK2,sK3,X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f2741,f120])).

fof(f2741,plain,(
    ! [X2,X3] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,k1_yellow_0(sK2,X3)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK3))
      | r4_waybel_0(sK2,sK3,X2,X3)
      | ~ v1_funct_1(X2)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f2726,f121])).

fof(f2726,plain,(
    ! [X2,X3] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X2,k1_yellow_0(sK2,X3)) != k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK3))
      | r4_waybel_0(sK2,sK3,X2,X3)
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(superposition,[],[f608,f691])).

fof(f608,plain,(
    ! [X17,X18,X16] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(X16),X17,k1_yellow_0(sK2,X18)) != k1_yellow_0(X16,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X16),X17,X18))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X16))))
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(X16,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X16),X17,X18))
      | ~ v1_funct_2(X17,u1_struct_0(sK0),u1_struct_0(X16))
      | r4_waybel_0(sK2,X16,X17,X18)
      | ~ v1_funct_1(X17)
      | ~ l1_orders_2(X16)
      | v2_struct_0(X16) ) ),
    inference(forward_demodulation,[],[f607,f523])).

fof(f607,plain,(
    ! [X17,X18,X16] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X16))))
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(X16,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X16),X17,X18))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(X16),X17,k1_yellow_0(sK2,X18)) != k1_yellow_0(X16,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X16),X17,X18))
      | r4_waybel_0(sK2,X16,X17,X18)
      | ~ v1_funct_2(X17,u1_struct_0(sK2),u1_struct_0(X16))
      | ~ v1_funct_1(X17)
      | ~ l1_orders_2(X16)
      | v2_struct_0(X16) ) ),
    inference(forward_demodulation,[],[f606,f523])).

fof(f606,plain,(
    ! [X17,X18,X16] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(X16,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X16),X17,X18))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(X16),X17,k1_yellow_0(sK2,X18)) != k1_yellow_0(X16,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X16),X17,X18))
      | r4_waybel_0(sK2,X16,X17,X18)
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X16))))
      | ~ v1_funct_2(X17,u1_struct_0(sK2),u1_struct_0(X16))
      | ~ v1_funct_1(X17)
      | ~ l1_orders_2(X16)
      | v2_struct_0(X16) ) ),
    inference(forward_demodulation,[],[f605,f523])).

fof(f605,plain,(
    ! [X17,X18,X16] :
      ( ~ r1_yellow_0(X16,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X16),X17,X18))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(X16),X17,k1_yellow_0(sK2,X18)) != k1_yellow_0(X16,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X16),X17,X18))
      | r4_waybel_0(sK2,X16,X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X16))))
      | ~ v1_funct_2(X17,u1_struct_0(sK2),u1_struct_0(X16))
      | ~ v1_funct_1(X17)
      | ~ l1_orders_2(X16)
      | v2_struct_0(X16) ) ),
    inference(forward_demodulation,[],[f604,f523])).

fof(f604,plain,(
    ! [X17,X18,X16] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(X16),X17,k1_yellow_0(sK2,X18)) != k1_yellow_0(X16,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X16),X17,X18))
      | r4_waybel_0(sK2,X16,X17,X18)
      | ~ r1_yellow_0(X16,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X16),X17,X18))
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X16))))
      | ~ v1_funct_2(X17,u1_struct_0(sK2),u1_struct_0(X16))
      | ~ v1_funct_1(X17)
      | ~ l1_orders_2(X16)
      | v2_struct_0(X16) ) ),
    inference(subsumption_resolution,[],[f603,f118])).

fof(f603,plain,(
    ! [X17,X18,X16] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(X16),X17,k1_yellow_0(sK2,X18)) != k1_yellow_0(X16,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X16),X17,X18))
      | r4_waybel_0(sK2,X16,X17,X18)
      | ~ r1_yellow_0(X16,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X16),X17,X18))
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X16))))
      | ~ v1_funct_2(X17,u1_struct_0(sK2),u1_struct_0(X16))
      | ~ v1_funct_1(X17)
      | ~ l1_orders_2(X16)
      | v2_struct_0(X16)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f579,f119])).

fof(f579,plain,(
    ! [X17,X18,X16] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(X16),X17,k1_yellow_0(sK2,X18)) != k1_yellow_0(X16,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X16),X17,X18))
      | r4_waybel_0(sK2,X16,X17,X18)
      | ~ r1_yellow_0(X16,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X16),X17,X18))
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X16))))
      | ~ v1_funct_2(X17,u1_struct_0(sK2),u1_struct_0(X16))
      | ~ v1_funct_1(X17)
      | ~ l1_orders_2(X16)
      | v2_struct_0(X16)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f152,f523])).

fof(f5862,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f5861,f1109])).

fof(f5861,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r1_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f5858,f131])).

fof(f5858,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r1_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f5834,f1201])).

fof(f5834,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(resolution,[],[f5797,f363])).

fof(f5797,plain,
    ( r3_waybel_0(sK2,sK3,sK4,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f5796,f4116])).

fof(f5796,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(forward_demodulation,[],[f5795,f5582])).

fof(f5582,plain,(
    k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(global_subsumption,[],[f2656,f5476,f5581])).

fof(f5581,plain,
    ( ~ r1_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f5580,f3314])).

fof(f5580,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f5579,f5476])).

fof(f5579,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f5575,f1067])).

fof(f5575,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(superposition,[],[f5403,f3098])).

fof(f3098,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f3097,f2488])).

fof(f2488,plain,
    ( r2_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6)) ),
    inference(resolution,[],[f2279,f911])).

fof(f3097,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f3095,f2656])).

fof(f3095,plain,
    ( ~ r1_yellow_0(sK0,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(resolution,[],[f1364,f1067])).

fof(f1364,plain,
    ( r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f1362,f131])).

fof(f1362,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_yellow_0(sK0,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6)) ),
    inference(resolution,[],[f1260,f1353])).

fof(f5403,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(backward_demodulation,[],[f5344,f5173])).

fof(f5173,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f5172,f1352])).

fof(f5172,plain,
    ( r4_waybel_0(sK2,sK3,sK4,sK6)
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f5165,f131])).

fof(f5165,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | r4_waybel_0(sK2,sK3,sK4,sK6)
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f4641,f1355])).

fof(f5344,plain,(
    k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f5343,f1019])).

fof(f5343,plain,
    ( k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6)
    | r1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f5342,f131])).

fof(f5342,plain,
    ( k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6)
    | r1_yellow_0(sK2,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f5330,f2048])).

fof(f5330,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK4,sK6)
    | k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6) ),
    inference(resolution,[],[f5286,f389])).

fof(f5286,plain,
    ( r3_waybel_0(sK2,sK3,sK4,sK6)
    | k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f5264,f4723])).

fof(f4723,plain,
    ( k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f4722,f2306])).

fof(f2306,plain,
    ( r2_yellow_0(sK0,sK6)
    | k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6) ),
    inference(resolution,[],[f2255,f911])).

fof(f4722,plain,
    ( k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6)
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f4720,f131])).

fof(f4720,plain,
    ( k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6)
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f4719,f2694])).

fof(f4719,plain,
    ( r3_waybel_0(sK0,sK3,sK4,sK6)
    | k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f4718,f2658])).

fof(f2658,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f2655,f2306])).

fof(f2655,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6) ),
    inference(resolution,[],[f2193,f1019])).

fof(f4718,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r3_waybel_0(sK0,sK3,sK4,sK6)
    | k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f4717,f2306])).

fof(f4717,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r3_waybel_0(sK0,sK3,sK4,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f4714,f1019])).

fof(f4714,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r3_waybel_0(sK0,sK3,sK4,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | r1_yellow_0(sK2,sK6)
    | k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6) ),
    inference(superposition,[],[f4626,f2635])).

fof(f2635,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f2632,f2306])).

fof(f2632,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6) ),
    inference(resolution,[],[f2173,f1019])).

fof(f5264,plain,
    ( k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6)
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(backward_demodulation,[],[f5177,f4732])).

fof(f4732,plain,
    ( k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK2,sK6))
    | k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6)
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(subsumption_resolution,[],[f4726,f131])).

fof(f4726,plain,
    ( k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6)
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK2,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(resolution,[],[f4725,f4313])).

fof(f4725,plain,
    ( r2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f4724,f2306])).

fof(f4724,plain,
    ( k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6)
    | r2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f4721,f131])).

fof(f4721,plain,
    ( k1_yellow_0(sK0,sK6) = k1_yellow_0(sK2,sK6)
    | r2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f4719,f2426])).

fof(f5476,plain,
    ( r2_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(resolution,[],[f5408,f911])).

fof(f5408,plain,
    ( r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f5385,f4657])).

fof(f4657,plain,
    ( r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f4656,f2256])).

fof(f4656,plain,
    ( r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f4654,f131])).

fof(f4654,plain,
    ( r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f4612,f2569])).

fof(f4612,plain,
    ( r4_waybel_0(sK0,sK3,sK4,sK6)
    | r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f4609,f3314])).

fof(f4609,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r4_waybel_0(sK0,sK3,sK4,sK6)
    | r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(superposition,[],[f4606,f3098])).

fof(f5385,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(backward_demodulation,[],[f5344,f4675])).

fof(f4675,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f4674,f2222])).

fof(f4674,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r2_yellow_0(sK2,sK6)
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | r4_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(subsumption_resolution,[],[f4668,f131])).

fof(f4668,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r2_yellow_0(sK2,sK6)
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | r4_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(resolution,[],[f4659,f4229])).

fof(f4659,plain,
    ( r1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r2_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f4658,f2256])).

fof(f4658,plain,
    ( r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f4655,f131])).

fof(f4655,plain,
    ( r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f4612,f2315])).

fof(f2315,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK0,sK3,sK4,X0)
      | r1_yellow_0(sK3,k9_relat_1(sK4,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0) ) ),
    inference(forward_demodulation,[],[f2314,f245])).

fof(f2314,plain,(
    ! [X0] :
      ( r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f2313,f114])).

fof(f2313,plain,(
    ! [X0] :
      ( r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2312,f115])).

fof(f2312,plain,(
    ! [X0] :
      ( r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2307,f125])).

fof(f2307,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ r4_waybel_0(sK0,sK3,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK0,X0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f1219,f126])).

fof(f1219,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK1))
      | r1_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK1),sK4,X3))
      | ~ r4_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_yellow_0(X2,X3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(forward_demodulation,[],[f1218,f691])).

fof(f1218,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ r4_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_yellow_0(X2,X3)
      | r1_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,X3))
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(forward_demodulation,[],[f1217,f691])).

fof(f1217,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ r4_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_yellow_0(X2,X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK3))
      | r1_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,X3))
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1216,f120])).

fof(f1216,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ r4_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_yellow_0(X2,X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK3))
      | r1_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,X3))
      | v2_struct_0(sK3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1195,f121])).

fof(f1195,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ r4_waybel_0(X2,sK3,sK4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_yellow_0(X2,X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(sK3))
      | r1_yellow_0(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,X3))
      | ~ l1_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(superposition,[],[f208,f691])).

fof(f5795,plain,
    ( k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(forward_demodulation,[],[f5794,f5177])).

fof(f5794,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK2,sK6))
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(subsumption_resolution,[],[f5788,f131])).

fof(f5788,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK2,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(resolution,[],[f5765,f4313])).

fof(f5765,plain,
    ( r2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f5764,f2491])).

fof(f5764,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f5760,f131])).

fof(f5760,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f5604,f2426])).

fof(f5604,plain,
    ( r3_waybel_0(sK0,sK3,sK4,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f5603,f4116])).

fof(f5603,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | r3_waybel_0(sK0,sK3,sK4,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f5589,f5563])).

fof(f5589,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | r3_waybel_0(sK0,sK3,sK4,sK6)
    | ~ r1_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(backward_demodulation,[],[f5582,f4623])).

fof(f4623,plain,
    ( r3_waybel_0(sK0,sK3,sK4,sK6)
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r1_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f4622,f2491])).

fof(f4622,plain,
    ( r3_waybel_0(sK0,sK3,sK4,sK6)
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(subsumption_resolution,[],[f4619,f131])).

fof(f4619,plain,
    ( r3_waybel_0(sK0,sK3,sK4,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(resolution,[],[f3565,f1405])).

fof(f6141,plain,(
    k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(forward_demodulation,[],[f6140,f6084])).

fof(f6084,plain,(
    k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6)) ),
    inference(unit_resulting_resolution,[],[f5921,f131,f6069,f1260])).

fof(f6069,plain,(
    r4_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(unit_resulting_resolution,[],[f6066,f363])).

fof(f6066,plain,(
    r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(subsumption_resolution,[],[f6065,f5582])).

fof(f6065,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(forward_demodulation,[],[f6064,f5891])).

fof(f5891,plain,(
    k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f5890,f3861])).

fof(f3861,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f3853,f2488])).

fof(f3853,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(duplicate_literal_removal,[],[f3851])).

fof(f3851,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f1996,f2633])).

fof(f1996,plain,
    ( ~ r1_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f1994,f131])).

fof(f1994,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f1371,f1260])).

fof(f5890,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f5878,f5471])).

fof(f5471,plain,
    ( r2_yellow_0(sK0,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(resolution,[],[f5407,f911])).

fof(f5407,plain,
    ( r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f5384,f4650])).

fof(f4650,plain,
    ( r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f4649,f2256])).

fof(f4649,plain,
    ( r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f4647,f131])).

fof(f4647,plain,
    ( r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f4611,f2569])).

fof(f4611,plain,
    ( r4_waybel_0(sK0,sK3,sK4,sK6)
    | r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f4608,f2304])).

fof(f4608,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r4_waybel_0(sK0,sK3,sK4,sK6)
    | r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(superposition,[],[f4606,f3861])).

fof(f5384,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(backward_demodulation,[],[f5344,f4667])).

fof(f4667,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f4666,f2222])).

fof(f4666,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | r2_yellow_0(sK2,sK6)
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | r4_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(subsumption_resolution,[],[f4660,f131])).

fof(f4660,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | r2_yellow_0(sK2,sK6)
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | r4_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(resolution,[],[f4652,f4229])).

fof(f4652,plain,
    ( r1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | r2_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f4651,f2256])).

fof(f4651,plain,
    ( r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | r1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f4648,f131])).

fof(f4648,plain,
    ( r2_yellow_0(sK2,sK6)
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | r1_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f4611,f2315])).

fof(f5878,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(backward_demodulation,[],[f5863,f5401])).

fof(f5401,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(backward_demodulation,[],[f5344,f5169])).

fof(f5169,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f5168,f1370])).

fof(f5168,plain,
    ( r4_waybel_0(sK2,sK3,sK4,sK6)
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f5167,f2633])).

fof(f5167,plain,
    ( r4_waybel_0(sK2,sK3,sK4,sK6)
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f5163,f131])).

fof(f5163,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | r4_waybel_0(sK2,sK3,sK4,sK6)
    | k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f4641,f1997])).

fof(f6064,plain,
    ( k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(forward_demodulation,[],[f6063,f5177])).

fof(f6063,plain,
    ( k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK2,sK6))
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(subsumption_resolution,[],[f6056,f131])).

fof(f6056,plain,
    ( k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK2,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(resolution,[],[f6002,f4313])).

fof(f6002,plain,(
    r2_yellow_0(sK3,k9_relat_1(sK4,sK6)) ),
    inference(forward_demodulation,[],[f5999,f245])).

fof(f5999,plain,(
    r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) ),
    inference(unit_resulting_resolution,[],[f114,f115,f5898,f131,f125,f126,f5985,f1248])).

fof(f5985,plain,(
    r3_waybel_0(sK0,sK3,sK4,sK6) ),
    inference(subsumption_resolution,[],[f5984,f5582])).

fof(f5984,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r3_waybel_0(sK0,sK3,sK4,sK6) ),
    inference(forward_demodulation,[],[f5983,f5891])).

fof(f5983,plain,
    ( r3_waybel_0(sK0,sK3,sK4,sK6)
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f5982,f131])).

fof(f5982,plain,
    ( r3_waybel_0(sK0,sK3,sK4,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f5976,f5898])).

fof(f5976,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | r3_waybel_0(sK0,sK3,sK4,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6)) ),
    inference(resolution,[],[f5897,f3565])).

fof(f5897,plain,
    ( r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f5896,f5415])).

fof(f5415,plain,
    ( r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6)) ),
    inference(subsumption_resolution,[],[f5414,f2488])).

fof(f5414,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(forward_demodulation,[],[f5413,f5344])).

fof(f5413,plain,
    ( r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK2,sK6)) ),
    inference(subsumption_resolution,[],[f5412,f2174])).

fof(f5412,plain,
    ( r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | ~ r1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f5411,f888])).

fof(f5411,plain,
    ( r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | ~ r1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f5409,f131])).

fof(f5409,plain,
    ( r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) = k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | ~ r1_yellow_0(sK2,sK6) ),
    inference(resolution,[],[f5406,f2463])).

fof(f2463,plain,(
    ! [X0] :
      ( ~ r4_waybel_0(sK2,sK1,sK4,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_yellow_0(sK1,k9_relat_1(sK4,X0)) = k1_funct_1(sK4,k1_yellow_0(sK2,X0))
      | ~ r1_yellow_0(sK2,X0) ) ),
    inference(forward_demodulation,[],[f2462,f653])).

fof(f2462,plain,(
    ! [X0] :
      ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK2,X0)) = k1_yellow_0(sK1,k9_relat_1(sK4,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r4_waybel_0(sK2,sK1,sK4,X0)
      | ~ r1_yellow_0(sK2,X0) ) ),
    inference(forward_demodulation,[],[f2461,f245])).

fof(f2461,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK2,X0)) = k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ r4_waybel_0(sK2,sK1,sK4,X0)
      | ~ r1_yellow_0(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f2460,f116])).

fof(f2460,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK2,X0)) = k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ r4_waybel_0(sK2,sK1,sK4,X0)
      | ~ r1_yellow_0(sK2,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f2459,f117])).

fof(f2459,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK2,X0)) = k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ r4_waybel_0(sK2,sK1,sK4,X0)
      | ~ r1_yellow_0(sK2,X0)
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f2454,f125])).

fof(f2454,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK2,X0)) = k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ r4_waybel_0(sK2,sK1,sK4,X0)
      | ~ r1_yellow_0(sK2,X0)
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f1265,f126])).

fof(f1265,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k1_yellow_0(sK2,X1)) = k1_yellow_0(X0,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK4,X1))
      | ~ r4_waybel_0(sK2,X0,sK4,X1)
      | ~ r1_yellow_0(sK2,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f1264,f523])).

fof(f1264,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ r4_waybel_0(sK2,X0,sK4,X1)
      | ~ r1_yellow_0(sK2,X1)
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0),sK4,k1_yellow_0(sK2,X1)) = k1_yellow_0(X0,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4,X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f1263,f523])).

fof(f1263,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ r4_waybel_0(sK2,X0,sK4,X1)
      | ~ r1_yellow_0(sK2,X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0),sK4,k1_yellow_0(sK2,X1)) = k1_yellow_0(X0,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4,X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f1262,f523])).

fof(f1262,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ r4_waybel_0(sK2,X0,sK4,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_yellow_0(sK2,X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0),sK4,k1_yellow_0(sK2,X1)) = k1_yellow_0(X0,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4,X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f1261,f118])).

fof(f1261,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ r4_waybel_0(sK2,X0,sK4,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_yellow_0(sK2,X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0),sK4,k1_yellow_0(sK2,X1)) = k1_yellow_0(X0,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4,X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1250,f119])).

fof(f1250,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ r4_waybel_0(sK2,X0,sK4,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_yellow_0(sK2,X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0),sK4,k1_yellow_0(sK2,X1)) = k1_yellow_0(X0,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4,X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f209,f523])).

fof(f5406,plain,
    ( r4_waybel_0(sK2,sK1,sK4,sK6)
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f5358,f1364])).

fof(f5358,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | r4_waybel_0(sK2,sK1,sK4,sK6)
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(backward_demodulation,[],[f5344,f3532])).

fof(f3532,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | r4_waybel_0(sK2,sK1,sK4,sK6)
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f3528,f131])).

fof(f3528,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | r4_waybel_0(sK2,sK1,sK4,sK6)
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f2735,f1355])).

fof(f2735,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK1,k9_relat_1(sK4,X0))
      | k1_yellow_0(sK1,k9_relat_1(sK4,X0)) != k1_funct_1(sK4,k1_yellow_0(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r4_waybel_0(sK2,sK1,sK4,X0) ) ),
    inference(forward_demodulation,[],[f2734,f245])).

fof(f2734,plain,(
    ! [X0] :
      ( k1_yellow_0(sK1,k9_relat_1(sK4,X0)) != k1_funct_1(sK4,k1_yellow_0(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | r4_waybel_0(sK2,sK1,sK4,X0) ) ),
    inference(forward_demodulation,[],[f2733,f245])).

fof(f2733,plain,(
    ! [X0] :
      ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k1_funct_1(sK4,k1_yellow_0(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | r4_waybel_0(sK2,sK1,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f2732,f116])).

fof(f2732,plain,(
    ! [X0] :
      ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k1_funct_1(sK4,k1_yellow_0(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | r4_waybel_0(sK2,sK1,sK4,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f2731,f117])).

fof(f2731,plain,(
    ! [X0] :
      ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k1_funct_1(sK4,k1_yellow_0(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | r4_waybel_0(sK2,sK1,sK4,X0)
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f2730,f124])).

fof(f2730,plain,(
    ! [X0] :
      ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k1_funct_1(sK4,k1_yellow_0(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | r4_waybel_0(sK2,sK1,sK4,X0)
      | ~ v1_funct_1(sK4)
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f2729,f125])).

fof(f2729,plain,(
    ! [X0] :
      ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k1_funct_1(sK4,k1_yellow_0(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | r4_waybel_0(sK2,sK1,sK4,X0)
      | ~ v1_funct_1(sK4)
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f2724,f126])).

fof(f2724,plain,(
    ! [X0] :
      ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) != k1_funct_1(sK4,k1_yellow_0(sK2,X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | r4_waybel_0(sK2,sK1,sK4,X0)
      | ~ v1_funct_1(sK4)
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(superposition,[],[f608,f653])).

fof(f5896,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f5880,f5676])).

fof(f5676,plain,
    ( r1_yellow_0(sK0,sK6)
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f5658,f888])).

fof(f5658,plain,
    ( r1_yellow_0(sK2,sK6)
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f5657,f131])).

fof(f5657,plain,
    ( r1_yellow_0(sK2,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f5656])).

fof(f5656,plain,
    ( r1_yellow_0(sK2,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | r1_yellow_0(sK2,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f5647,f2048])).

fof(f5647,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK4,sK6)
    | r1_yellow_0(sK2,sK6)
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f5626,f389])).

fof(f5626,plain,
    ( r3_waybel_0(sK2,sK3,sK4,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | r1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f5625,f2173])).

fof(f5625,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | r1_yellow_0(sK2,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(forward_demodulation,[],[f5624,f5582])).

fof(f5624,plain,
    ( k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | r1_yellow_0(sK2,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(forward_demodulation,[],[f5623,f5177])).

fof(f5623,plain,
    ( r1_yellow_0(sK2,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK2,sK6))
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(subsumption_resolution,[],[f5617,f131])).

fof(f5617,plain,
    ( r1_yellow_0(sK2,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | k2_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK2,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | r3_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(resolution,[],[f5616,f4313])).

fof(f5616,plain,
    ( r2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | r1_yellow_0(sK2,sK6)
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(subsumption_resolution,[],[f5612,f131])).

fof(f5612,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | r1_yellow_0(sK2,sK6)
    | r2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f5611])).

fof(f5611,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | r1_yellow_0(sK2,sK6)
    | r2_yellow_0(sK3,k9_relat_1(sK4,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(resolution,[],[f5606,f2426])).

fof(f5606,plain,
    ( r3_waybel_0(sK0,sK3,sK4,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | r1_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f5591,f2173])).

fof(f5591,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k2_yellow_0(sK0,sK6))
    | r3_waybel_0(sK0,sK3,sK4,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | r1_yellow_0(sK2,sK6) ),
    inference(backward_demodulation,[],[f5582,f4626])).

fof(f5880,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | r2_yellow_0(sK1,k9_relat_1(sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6) ),
    inference(backward_demodulation,[],[f5863,f5403])).

fof(f5898,plain,(
    r2_yellow_0(sK0,sK6) ),
    inference(unit_resulting_resolution,[],[f5895,f911])).

fof(f5895,plain,(
    r2_yellow_0(sK2,sK6) ),
    inference(subsumption_resolution,[],[f5879,f2279])).

fof(f5879,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | r2_yellow_0(sK2,sK6) ),
    inference(backward_demodulation,[],[f5863,f5402])).

fof(f5402,plain,
    ( k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK0,sK6))
    | r2_yellow_0(sK2,sK6) ),
    inference(backward_demodulation,[],[f5344,f5171])).

fof(f5921,plain,(
    r1_yellow_0(sK0,sK6) ),
    inference(unit_resulting_resolution,[],[f5898,f5676])).

fof(f6140,plain,(
    k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK0,sK6)) ),
    inference(forward_demodulation,[],[f6126,f5344])).

fof(f6126,plain,(
    k1_yellow_0(sK3,k9_relat_1(sK4,sK6)) != k1_funct_1(sK4,k1_yellow_0(sK2,sK6)) ),
    inference(unit_resulting_resolution,[],[f131,f6068,f6093,f4641])).

fof(f6093,plain,(
    r1_yellow_0(sK1,k9_relat_1(sK4,sK6)) ),
    inference(forward_demodulation,[],[f6088,f245])).

fof(f6088,plain,(
    r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) ),
    inference(unit_resulting_resolution,[],[f114,f115,f116,f117,f124,f5921,f131,f125,f126,f6069,f149])).

fof(f6068,plain,(
    ~ r4_waybel_0(sK2,sK3,sK4,sK6) ),
    inference(unit_resulting_resolution,[],[f6066,f389])).
%------------------------------------------------------------------------------
