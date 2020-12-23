%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:37 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  228 (2404 expanded)
%              Number of clauses        :  159 ( 504 expanded)
%              Number of leaves         :   20 ( 980 expanded)
%              Depth                    :   28
%              Number of atoms          : 1094 (32883 expanded)
%              Number of equality atoms :  453 (7854 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( r1_orders_2(X1,X5,X6)
                      | k1_funct_1(X2,X4) != X6
                      | k1_funct_1(X2,X3) != X5
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              | ~ r1_orders_2(X0,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_orders_2(X1,X5,X6)
                        & k1_funct_1(X2,X4) = X6
                        & k1_funct_1(X2,X3) = X5
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                & r1_orders_2(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( ! [X6] :
                        ( r1_orders_2(X1,X5,X6)
                        | k1_funct_1(X2,X4) != X6
                        | k1_funct_1(X2,X3) != X5
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_orders_2(X0,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_orders_2(X0,X5,X6)
                        & k1_funct_1(X1,X4) = X6
                        & k1_funct_1(X1,X3) = X5
                        & m1_subset_1(X6,u1_struct_0(X0)) )
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X2,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X2)) )
            & m1_subset_1(X3,u1_struct_0(X2)) ) )
      & ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( ! [X10] :
                        ( r1_orders_2(X0,X9,X10)
                        | k1_funct_1(X1,X8) != X10
                        | k1_funct_1(X1,X7) != X9
                        | ~ m1_subset_1(X10,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                | ~ r1_orders_2(X2,X7,X8)
                | ~ m1_subset_1(X8,u1_struct_0(X2)) )
            | ~ m1_subset_1(X7,u1_struct_0(X2)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f21])).

fof(f26,plain,(
    ! [X4,X5,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ~ r1_orders_2(X0,X5,X6)
          & k1_funct_1(X1,X4) = X6
          & k1_funct_1(X1,X3) = X5
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X5,sK5(X0,X1,X2))
        & k1_funct_1(X1,X4) = sK5(X0,X1,X2)
        & k1_funct_1(X1,X3) = X5
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_orders_2(X0,X5,X6)
              & k1_funct_1(X1,X4) = X6
              & k1_funct_1(X1,X3) = X5
              & m1_subset_1(X6,u1_struct_0(X0)) )
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ? [X6] :
            ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X6)
            & k1_funct_1(X1,X4) = X6
            & k1_funct_1(X1,X3) = sK4(X0,X1,X2)
            & m1_subset_1(X6,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_orders_2(X0,X5,X6)
                  & k1_funct_1(X1,X4) = X6
                  & k1_funct_1(X1,X3) = X5
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              & m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_orders_2(X2,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_orders_2(X0,X5,X6)
                & k1_funct_1(X1,sK3(X0,X1,X2)) = X6
                & k1_funct_1(X1,X3) = X5
                & m1_subset_1(X6,u1_struct_0(X0)) )
            & m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_orders_2(X2,X3,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_orders_2(X0,X5,X6)
                      & k1_funct_1(X1,X4) = X6
                      & k1_funct_1(X1,X3) = X5
                      & m1_subset_1(X6,u1_struct_0(X0)) )
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_orders_2(X2,X3,X4)
              & m1_subset_1(X4,u1_struct_0(X2)) )
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_orders_2(X0,X5,X6)
                    & k1_funct_1(X1,X4) = X6
                    & k1_funct_1(X1,sK2(X0,X1,X2)) = X5
                    & m1_subset_1(X6,u1_struct_0(X0)) )
                & m1_subset_1(X5,u1_struct_0(X0)) )
            & r1_orders_2(X2,sK2(X0,X1,X2),X4)
            & m1_subset_1(X4,u1_struct_0(X2)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2))
          & k1_funct_1(X1,sK3(X0,X1,X2)) = sK5(X0,X1,X2)
          & k1_funct_1(X1,sK2(X0,X1,X2)) = sK4(X0,X1,X2)
          & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
          & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
          & r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2))
          & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2))
          & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) ) )
      & ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( ! [X10] :
                        ( r1_orders_2(X0,X9,X10)
                        | k1_funct_1(X1,X8) != X10
                        | k1_funct_1(X1,X7) != X9
                        | ~ m1_subset_1(X10,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                | ~ r1_orders_2(X2,X7,X8)
                | ~ m1_subset_1(X8,u1_struct_0(X2)) )
            | ~ m1_subset_1(X7,u1_struct_0(X2)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f26,f25,f24,f23])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ! [X2] :
              ( ( l1_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( l1_orders_2(X3)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                         => ( ( v5_orders_3(X4,X0,X1)
                              & X4 = X5
                              & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                              & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                           => v5_orders_3(X5,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ! [X2] :
                ( ( l1_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( l1_orders_2(X3)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(X5) )
                           => ( ( v5_orders_3(X4,X0,X1)
                                & X4 = X5
                                & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                                & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                             => v5_orders_3(X5,X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ! [X2] :
                ( l1_orders_2(X2)
               => ! [X3] :
                    ( l1_orders_2(X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(X5) )
                           => ( ( v5_orders_3(X4,X0,X1)
                                & X4 = X5
                                & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                                & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                             => v5_orders_3(X5,X2,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ v5_orders_3(X5,X2,X3)
                          & v5_orders_3(X4,X0,X1)
                          & X4 = X5
                          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & l1_orders_2(X3) )
              & l1_orders_2(X2) )
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ v5_orders_3(X5,X2,X3)
                          & v5_orders_3(X4,X0,X1)
                          & X4 = X5
                          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & l1_orders_2(X3) )
              & l1_orders_2(X2) )
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ v5_orders_3(X5,X2,X3)
          & v5_orders_3(X4,X0,X1)
          & X4 = X5
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
          & v1_funct_1(X5) )
     => ( ~ v5_orders_3(sK11,X2,X3)
        & v5_orders_3(X4,X0,X1)
        & sK11 = X4
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
        & v1_funct_2(sK11,u1_struct_0(X2),u1_struct_0(X3))
        & v1_funct_1(sK11) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ v5_orders_3(X5,X2,X3)
              & v5_orders_3(X4,X0,X1)
              & X4 = X5
              & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
              & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ~ v5_orders_3(X5,X2,X3)
            & v5_orders_3(sK10,X0,X1)
            & sK10 = X5
            & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
            & v1_funct_1(X5) )
        & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK10,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ v5_orders_3(X5,X2,X3)
                  & v5_orders_3(X4,X0,X1)
                  & X4 = X5
                  & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                  & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & l1_orders_2(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ v5_orders_3(X5,X2,sK9)
                & v5_orders_3(X4,X0,X1)
                & X4 = X5
                & g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
                & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK9))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK9))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & l1_orders_2(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ v5_orders_3(X5,X2,X3)
                      & v5_orders_3(X4,X0,X1)
                      & X4 = X5
                      & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                      & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & l1_orders_2(X3) )
          & l1_orders_2(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ v5_orders_3(X5,sK8,X3)
                    & v5_orders_3(X4,X0,X1)
                    & X4 = X5
                    & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                    & g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X3))))
                    & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(X3))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & l1_orders_2(X3) )
        & l1_orders_2(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ v5_orders_3(X5,X2,X3)
                          & v5_orders_3(X4,X0,X1)
                          & X4 = X5
                          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & l1_orders_2(X3) )
              & l1_orders_2(X2) )
          & l1_orders_2(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ v5_orders_3(X5,X2,X3)
                        & v5_orders_3(X4,X0,sK7)
                        & X4 = X5
                        & g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                        & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK7))
                    & v1_funct_1(X4) )
                & l1_orders_2(X3) )
            & l1_orders_2(X2) )
        & l1_orders_2(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ v5_orders_3(X5,X2,X3)
                            & v5_orders_3(X4,X0,X1)
                            & X4 = X5
                            & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & l1_orders_2(X3) )
                & l1_orders_2(X2) )
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ v5_orders_3(X5,X2,X3)
                          & v5_orders_3(X4,sK6,X1)
                          & X4 = X5
                          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                          & g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & l1_orders_2(X3) )
              & l1_orders_2(X2) )
          & l1_orders_2(X1) )
      & l1_orders_2(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ v5_orders_3(sK11,sK8,sK9)
    & v5_orders_3(sK10,sK6,sK7)
    & sK10 = sK11
    & g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9))
    & g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8))
    & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
    & v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9))
    & v1_funct_1(sK11)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    & v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7))
    & v1_funct_1(sK10)
    & l1_orders_2(sK9)
    & l1_orders_2(sK8)
    & l1_orders_2(sK7)
    & l1_orders_2(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f15,f33,f32,f31,f30,f29,f28])).

fof(f62,plain,(
    g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f38,plain,(
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
    inference(cnf_transformation,[],[f11])).

fof(f69,plain,(
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
    inference(equality_resolution,[],[f38])).

fof(f70,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f54,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f34])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | k1_funct_1(X1,sK2(X0,X1,X2)) = sK4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,plain,(
    ! [X0,X2,X1] :
      ( ( v5_orders_3(X2,X0,X1)
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f19,plain,(
    ! [X0,X2,X1] :
      ( ( ( v5_orders_3(X2,X0,X1)
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ v5_orders_3(X2,X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_orders_3(X1,X0,X2)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v5_orders_3(X1,X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f19])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v5_orders_3(X1,X0,X2)
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    ~ v5_orders_3(sK11,sK8,sK9) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_orders_3(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r1_orders_2(X0,X3,X4)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X1))
                                 => ( ( k1_funct_1(X2,X4) = X6
                                      & k1_funct_1(X2,X3) = X5 )
                                   => r1_orders_2(X1,X5,X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_orders_3(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( ! [X6] :
                                ( r1_orders_2(X1,X5,X6)
                                | k1_funct_1(X2,X4) != X6
                                | k1_funct_1(X2,X3) != X5
                                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        | ~ r1_orders_2(X0,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_orders_3(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( ! [X6] :
                                ( r1_orders_2(X1,X5,X6)
                                | k1_funct_1(X2,X4) != X6
                                | k1_funct_1(X2,X3) != X5
                                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        | ~ r1_orders_2(X0,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f13,f17,f16])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | k1_funct_1(X1,sK3(X0,X1,X2)) = sK5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | ~ v5_orders_3(X1,X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    v5_orders_3(sK10,sK6,sK7) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    sK10 = sK11 ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    ! [X2,X0,X10,X8,X7,X1,X9] :
      ( r1_orders_2(X0,X9,X10)
      | k1_funct_1(X1,X8) != X10
      | k1_funct_1(X1,X7) != X9
      | ~ m1_subset_1(X10,u1_struct_0(X0))
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | ~ r1_orders_2(X2,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r1_orders_2(X0,X9,k1_funct_1(X1,X8))
      | k1_funct_1(X1,X7) != X9
      | ~ m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0))
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | ~ r1_orders_2(X2,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f42])).

fof(f72,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r1_orders_2(X0,k1_funct_1(X1,X7),k1_funct_1(X1,X8))
      | ~ m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0))
      | ~ m1_subset_1(k1_funct_1(X1,X7),u1_struct_0(X0))
      | ~ r1_orders_2(X2,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f71])).

fof(f63,plain,(
    g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_12,plain,
    ( sP0(X0,X1,X2)
    | r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2388,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2387,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_21,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2395,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3127,plain,
    ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK6) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_2395])).

cnf(c_31,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_0,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_87,plain,
    ( m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3129,plain,
    ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK6) = X0
    | m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_2395])).

cnf(c_3164,plain,
    ( ~ m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
    | g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK6) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3129])).

cnf(c_3293,plain,
    ( u1_struct_0(sK6) = X0
    | g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3127,c_31,c_87,c_3164])).

cnf(c_3294,plain,
    ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK6) = X0 ),
    inference(renaming,[status(thm)],[c_3293])).

cnf(c_3300,plain,
    ( u1_struct_0(sK8) = u1_struct_0(sK6) ),
    inference(equality_resolution,[status(thm)],[c_3294])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X3)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2394,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | r1_orders_2(X1,X2,X3) != iProver_top
    | r1_orders_2(X0,X2,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4002,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK6))
    | r1_orders_2(X0,X1,X2) != iProver_top
    | r1_orders_2(sK6,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3300,c_2394])).

cnf(c_3593,plain,
    ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) ),
    inference(demodulation,[status(thm)],[c_3300,c_21])).

cnf(c_4053,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8))
    | r1_orders_2(X0,X1,X2) != iProver_top
    | r1_orders_2(sK6,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK8)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4002,c_3300,c_3593])).

cnf(c_32,plain,
    ( l1_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5064,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r1_orders_2(sK6,X1,X2) = iProver_top
    | r1_orders_2(X0,X1,X2) != iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4053,c_32])).

cnf(c_5065,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8))
    | r1_orders_2(X0,X1,X2) != iProver_top
    | r1_orders_2(sK6,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK8)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5064])).

cnf(c_5078,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5065])).

cnf(c_29,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_34,plain,
    ( l1_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6463,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r1_orders_2(sK8,X0,X1) != iProver_top
    | r1_orders_2(sK6,X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5078,c_34])).

cnf(c_6464,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6463])).

cnf(c_6475,plain,
    ( sP0(X0,X1,sK8) = iProver_top
    | r1_orders_2(sK6,X2,sK3(X0,X1,sK8)) = iProver_top
    | r1_orders_2(sK8,X2,sK3(X0,X1,sK8)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2387,c_6464])).

cnf(c_9313,plain,
    ( sP0(X0,X1,sK8) = iProver_top
    | r1_orders_2(sK6,sK2(X0,X1,sK8),sK3(X0,X1,sK8)) = iProver_top
    | m1_subset_1(sK2(X0,X1,sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2388,c_6475])).

cnf(c_14,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3649,plain,
    ( sP0(X0,X1,sK8)
    | m1_subset_1(sK2(X0,X1,sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3665,plain,
    ( sP0(X0,X1,sK8) = iProver_top
    | m1_subset_1(sK2(X0,X1,sK8),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3649])).

cnf(c_9318,plain,
    ( r1_orders_2(sK6,sK2(X0,X1,sK8),sK3(X0,X1,sK8)) = iProver_top
    | sP0(X0,X1,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9313,c_3665])).

cnf(c_9319,plain,
    ( sP0(X0,X1,sK8) = iProver_top
    | r1_orders_2(sK6,sK2(X0,X1,sK8),sK3(X0,X1,sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9318])).

cnf(c_9,plain,
    ( sP0(X0,X1,X2)
    | k1_funct_1(X1,sK2(X0,X1,X2)) = sK4(X0,X1,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2391,plain,
    ( k1_funct_1(X0,sK2(X1,X0,X2)) = sK4(X1,X0,X2)
    | sP0(X1,X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | v5_orders_3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,negated_conjecture,
    ( ~ v5_orders_3(sK11,sK8,sK9) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_316,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | sK9 != X2
    | sK8 != X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_317,plain,
    ( ~ sP1(sK8,sK11,sK9)
    | ~ sP0(sK9,sK11,sK8) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | sP1(X1,X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_353,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
    | ~ v1_funct_1(X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X2)
    | u1_struct_0(X2) != u1_struct_0(sK9)
    | u1_struct_0(X0) != u1_struct_0(sK8)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_354,plain,
    ( sP1(X0,sK11,X1)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK11)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK9)
    | u1_struct_0(X0) != u1_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_358,plain,
    ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | sP1(X0,sK11,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK9)
    | u1_struct_0(X0) != u1_struct_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_24])).

cnf(c_359,plain,
    ( sP1(X0,sK11,X1)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK9)
    | u1_struct_0(X0) != u1_struct_0(sK8) ),
    inference(renaming,[status(thm)],[c_358])).

cnf(c_427,plain,
    ( ~ sP0(sK9,sK11,sK8)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK9)
    | u1_struct_0(X0) != u1_struct_0(sK8)
    | sK9 != X1
    | sK8 != X0
    | sK11 != sK11 ),
    inference(resolution_lifted,[status(thm)],[c_317,c_359])).

cnf(c_428,plain,
    ( ~ sP0(sK9,sK11,sK8)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
    | ~ l1_orders_2(sK9)
    | ~ l1_orders_2(sK8)
    | u1_struct_0(sK9) != u1_struct_0(sK9)
    | u1_struct_0(sK8) != u1_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_28,negated_conjecture,
    ( l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_430,plain,
    ( ~ sP0(sK9,sK11,sK8)
    | u1_struct_0(sK9) != u1_struct_0(sK9)
    | u1_struct_0(sK8) != u1_struct_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_428,c_29,c_28,c_22])).

cnf(c_1038,plain,
    ( ~ sP0(sK9,sK11,sK8) ),
    inference(equality_resolution_simp,[status(thm)],[c_430])).

cnf(c_2377,plain,
    ( sP0(sK9,sK11,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1038])).

cnf(c_3509,plain,
    ( k1_funct_1(sK11,sK2(sK9,sK11,sK8)) = sK4(sK9,sK11,sK8) ),
    inference(superposition,[status(thm)],[c_2391,c_2377])).

cnf(c_8,plain,
    ( sP0(X0,X1,X2)
    | k1_funct_1(X1,sK3(X0,X1,X2)) = sK5(X0,X1,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2392,plain,
    ( k1_funct_1(X0,sK3(X1,X0,X2)) = sK5(X1,X0,X2)
    | sP0(X1,X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3531,plain,
    ( k1_funct_1(sK11,sK3(sK9,sK11,sK8)) = sK5(sK9,sK11,sK8) ),
    inference(superposition,[status(thm)],[c_2392,c_2377])).

cnf(c_6,plain,
    ( ~ sP1(X0,X1,X2)
    | sP0(X2,X1,X0)
    | ~ v5_orders_3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,negated_conjecture,
    ( v5_orders_3(sK10,sK6,sK7) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_326,plain,
    ( ~ sP1(X0,X1,X2)
    | sP0(X2,X1,X0)
    | sK7 != X2
    | sK6 != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_327,plain,
    ( ~ sP1(sK6,sK10,sK7)
    | sP0(sK7,sK10,sK6) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_464,plain,
    ( sP0(sK7,sK10,sK6)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK9)
    | u1_struct_0(X0) != u1_struct_0(sK8)
    | sK7 != X1
    | sK6 != X0
    | sK10 != sK11 ),
    inference(resolution_lifted,[status(thm)],[c_327,c_359])).

cnf(c_465,plain,
    ( sP0(sK7,sK10,sK6)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ l1_orders_2(sK7)
    | ~ l1_orders_2(sK6)
    | u1_struct_0(sK7) != u1_struct_0(sK9)
    | u1_struct_0(sK6) != u1_struct_0(sK8)
    | sK10 != sK11 ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_30,negated_conjecture,
    ( l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,negated_conjecture,
    ( sK10 = sK11 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_467,plain,
    ( u1_struct_0(sK6) != u1_struct_0(sK8)
    | u1_struct_0(sK7) != u1_struct_0(sK9)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | sP0(sK7,sK10,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_465,c_31,c_30,c_19])).

cnf(c_468,plain,
    ( sP0(sK7,sK10,sK6)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | u1_struct_0(sK7) != u1_struct_0(sK9)
    | u1_struct_0(sK6) != u1_struct_0(sK8) ),
    inference(renaming,[status(thm)],[c_467])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_383,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
    | ~ v1_funct_1(X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X2)
    | u1_struct_0(X2) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_384,plain,
    ( sP1(X0,sK10,X1)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK10)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_388,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | sP1(X0,sK10,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_384,c_27])).

cnf(c_389,plain,
    ( sP1(X0,sK10,X1)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(renaming,[status(thm)],[c_388])).

cnf(c_484,plain,
    ( sP0(sK7,sK10,sK6)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | sK7 != X1
    | sK6 != X0
    | sK10 != sK10 ),
    inference(resolution_lifted,[status(thm)],[c_327,c_389])).

cnf(c_485,plain,
    ( sP0(sK7,sK10,sK6)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ l1_orders_2(sK7)
    | ~ l1_orders_2(sK6)
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_487,plain,
    ( sP0(sK7,sK10,sK6)
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_485,c_31,c_30,c_25])).

cnf(c_1030,plain,
    ( sP0(sK7,sK10,sK6) ),
    inference(equality_resolution_simp,[status(thm)],[c_487])).

cnf(c_1033,plain,
    ( sP0(sK7,sK10,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_1030])).

cnf(c_2378,plain,
    ( sP0(sK7,sK10,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1033])).

cnf(c_2408,plain,
    ( sP0(sK7,sK11,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2378,c_19])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X3,X4)
    | r1_orders_2(X0,k1_funct_1(X1,X3),k1_funct_1(X1,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(k1_funct_1(X1,X4),u1_struct_0(X0))
    | ~ m1_subset_1(k1_funct_1(X1,X3),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2385,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r1_orders_2(X2,X3,X4) != iProver_top
    | r1_orders_2(X0,k1_funct_1(X1,X3),k1_funct_1(X1,X4)) = iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(k1_funct_1(X1,X4),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k1_funct_1(X1,X3),u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3373,plain,
    ( r1_orders_2(sK7,k1_funct_1(sK11,X0),k1_funct_1(sK11,X1)) = iProver_top
    | r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,X1),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2408,c_2385])).

cnf(c_20,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3126,plain,
    ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK7) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_2395])).

cnf(c_3173,plain,
    ( u1_struct_0(sK9) = u1_struct_0(sK7)
    | m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3126])).

cnf(c_3185,plain,
    ( ~ m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
    | u1_struct_0(sK9) = u1_struct_0(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3173])).

cnf(c_3833,plain,
    ( m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
    | ~ l1_orders_2(sK9) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3869,plain,
    ( u1_struct_0(sK9) = u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3173,c_28,c_3185,c_3833])).

cnf(c_4531,plain,
    ( r1_orders_2(sK7,k1_funct_1(sK11,X0),k1_funct_1(sK11,X1)) = iProver_top
    | r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,X1),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3373,c_3300,c_3869])).

cnf(c_4544,plain,
    ( r1_orders_2(sK7,k1_funct_1(sK11,X0),sK5(sK9,sK11,sK8)) = iProver_top
    | r1_orders_2(sK6,X0,sK3(sK9,sK11,sK8)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK3(sK9,sK11,sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,sK3(sK9,sK11,sK8)),u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3531,c_4531])).

cnf(c_4551,plain,
    ( r1_orders_2(sK7,k1_funct_1(sK11,X0),sK5(sK9,sK11,sK8)) = iProver_top
    | r1_orders_2(sK6,X0,sK3(sK9,sK11,sK8)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK3(sK9,sK11,sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4544,c_3531])).

cnf(c_766,plain,
    ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2))
    | u1_struct_0(sK9) != u1_struct_0(sK9)
    | u1_struct_0(sK8) != u1_struct_0(sK8)
    | sK9 != X0
    | sK8 != X2
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_430])).

cnf(c_767,plain,
    ( m1_subset_1(sK3(sK9,sK11,sK8),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_766])).

cnf(c_768,plain,
    ( m1_subset_1(sK3(sK9,sK11,sK8),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_767])).

cnf(c_10,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_835,plain,
    ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
    | u1_struct_0(sK9) != u1_struct_0(sK9)
    | u1_struct_0(sK8) != u1_struct_0(sK8)
    | sK9 != X0
    | sK8 != X2
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_430])).

cnf(c_836,plain,
    ( m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) ),
    inference(unflattening,[status(thm)],[c_835])).

cnf(c_837,plain,
    ( m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_836])).

cnf(c_7689,plain,
    ( r1_orders_2(sK7,k1_funct_1(sK11,X0),sK5(sK9,sK11,sK8)) = iProver_top
    | r1_orders_2(sK6,X0,sK3(sK9,sK11,sK8)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4551,c_768,c_837])).

cnf(c_7699,plain,
    ( r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
    | r1_orders_2(sK6,sK2(sK9,sK11,sK8),sK3(sK9,sK11,sK8)) != iProver_top
    | m1_subset_1(sK2(sK9,sK11,sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,sK2(sK9,sK11,sK8)),u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3509,c_7689])).

cnf(c_7752,plain,
    ( r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
    | r1_orders_2(sK6,sK2(sK9,sK11,sK8),sK3(sK9,sK11,sK8)) != iProver_top
    | m1_subset_1(sK2(sK9,sK11,sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7699,c_3509])).

cnf(c_33,plain,
    ( l1_orders_2(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_35,plain,
    ( l1_orders_2(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_743,plain,
    ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2))
    | u1_struct_0(sK9) != u1_struct_0(sK9)
    | u1_struct_0(sK8) != u1_struct_0(sK8)
    | sK9 != X0
    | sK8 != X2
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_430])).

cnf(c_744,plain,
    ( m1_subset_1(sK2(sK9,sK11,sK8),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_743])).

cnf(c_745,plain,
    ( m1_subset_1(sK2(sK9,sK11,sK8),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_11,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_812,plain,
    ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
    | u1_struct_0(sK9) != u1_struct_0(sK9)
    | u1_struct_0(sK8) != u1_struct_0(sK8)
    | sK9 != X0
    | sK8 != X2
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_430])).

cnf(c_813,plain,
    ( m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) ),
    inference(unflattening,[status(thm)],[c_812])).

cnf(c_814,plain,
    ( m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_813])).

cnf(c_7,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_900,plain,
    ( ~ r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2))
    | u1_struct_0(sK9) != u1_struct_0(sK9)
    | u1_struct_0(sK8) != u1_struct_0(sK8)
    | sK9 != X0
    | sK8 != X2
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_430])).

cnf(c_901,plain,
    ( ~ r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) ),
    inference(unflattening,[status(thm)],[c_900])).

cnf(c_902,plain,
    ( r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_901])).

cnf(c_3875,plain,
    ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
    inference(demodulation,[status(thm)],[c_3869,c_20])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2396,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4191,plain,
    ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK7) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3875,c_2396])).

cnf(c_2397,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3892,plain,
    ( m1_subset_1(u1_orders_2(sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)))) = iProver_top
    | l1_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3869,c_2397])).

cnf(c_4193,plain,
    ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK7) = X1
    | m1_subset_1(u1_orders_2(sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3875,c_2396])).

cnf(c_4432,plain,
    ( u1_orders_2(sK7) = X1
    | g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4191,c_33,c_3892,c_4193])).

cnf(c_4433,plain,
    ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK7) = X1 ),
    inference(renaming,[status(thm)],[c_4432])).

cnf(c_4438,plain,
    ( u1_orders_2(sK9) = u1_orders_2(sK7) ),
    inference(equality_resolution,[status(thm)],[c_4433])).

cnf(c_5255,plain,
    ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
    inference(demodulation,[status(thm)],[c_4438,c_3875])).

cnf(c_2915,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
    | X1 = u1_struct_0(sK9)
    | g1_orders_2(X1,X2) != g1_orders_2(u1_struct_0(sK9),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3832,plain,
    ( ~ m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
    | X0 = u1_struct_0(sK9)
    | g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
    inference(instantiation,[status(thm)],[c_2915])).

cnf(c_5621,plain,
    ( ~ m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
    | g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) != g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9))
    | u1_struct_0(sK7) = u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_3832])).

cnf(c_1995,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2685,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9))
    | X0 != sK5(sK9,sK11,sK8)
    | X1 != u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1995])).

cnf(c_2933,plain,
    ( m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9))
    | X0 != sK5(sK9,sK11,sK8)
    | u1_struct_0(X1) != u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2685])).

cnf(c_6023,plain,
    ( m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9))
    | X0 != sK5(sK9,sK11,sK8)
    | u1_struct_0(sK7) != u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2933])).

cnf(c_8491,plain,
    ( m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9))
    | sK5(sK9,sK11,sK8) != sK5(sK9,sK11,sK8)
    | u1_struct_0(sK7) != u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_6023])).

cnf(c_8493,plain,
    ( sK5(sK9,sK11,sK8) != sK5(sK9,sK11,sK8)
    | u1_struct_0(sK7) != u1_struct_0(sK9)
    | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8491])).

cnf(c_1989,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_8492,plain,
    ( sK5(sK9,sK11,sK8) = sK5(sK9,sK11,sK8) ),
    inference(instantiation,[status(thm)],[c_1989])).

cnf(c_2700,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9))
    | X0 != sK4(sK9,sK11,sK8)
    | X1 != u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1995])).

cnf(c_6028,plain,
    ( m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9))
    | X0 != sK4(sK9,sK11,sK8)
    | u1_struct_0(sK7) != u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2700])).

cnf(c_8501,plain,
    ( m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9))
    | sK4(sK9,sK11,sK8) != sK4(sK9,sK11,sK8)
    | u1_struct_0(sK7) != u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_6028])).

cnf(c_8503,plain,
    ( sK4(sK9,sK11,sK8) != sK4(sK9,sK11,sK8)
    | u1_struct_0(sK7) != u1_struct_0(sK9)
    | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8501])).

cnf(c_8502,plain,
    ( sK4(sK9,sK11,sK8) = sK4(sK9,sK11,sK8) ),
    inference(instantiation,[status(thm)],[c_1989])).

cnf(c_1990,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_4705,plain,
    ( g1_orders_2(X0,X1) != X2
    | g1_orders_2(X0,X1) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != X2 ),
    inference(instantiation,[status(thm)],[c_1990])).

cnf(c_7638,plain,
    ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | g1_orders_2(X0,X1) = g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(X2,X3) ),
    inference(instantiation,[status(thm)],[c_4705])).

cnf(c_13464,plain,
    ( g1_orders_2(X0,X1) = g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7))
    | g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9))
    | g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) != g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
    inference(instantiation,[status(thm)],[c_7638])).

cnf(c_13960,plain,
    ( g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) != g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9))
    | g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) = g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7))
    | g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
    inference(instantiation,[status(thm)],[c_13464])).

cnf(c_2675,plain,
    ( ~ r1_orders_2(X0,X1,sK5(sK9,sK11,sK8))
    | r1_orders_2(sK9,X1,sK5(sK9,sK11,sK8))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(X0))
    | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(sK9)
    | g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2977,plain,
    ( ~ r1_orders_2(X0,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8))
    | r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8))
    | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(X0))
    | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9))
    | ~ m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(X0))
    | ~ m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(sK9)
    | g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(instantiation,[status(thm)],[c_2675])).

cnf(c_14980,plain,
    ( ~ r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8))
    | r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8))
    | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9))
    | ~ m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9))
    | ~ l1_orders_2(sK7)
    | ~ l1_orders_2(sK9)
    | g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) ),
    inference(instantiation,[status(thm)],[c_2977])).

cnf(c_14984,plain,
    ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7))
    | r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) != iProver_top
    | r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
    | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top
    | l1_orders_2(sK7) != iProver_top
    | l1_orders_2(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14980])).

cnf(c_15665,plain,
    ( r1_orders_2(sK6,sK2(sK9,sK11,sK8),sK3(sK9,sK11,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7752,c_33,c_28,c_35,c_20,c_745,c_814,c_837,c_902,c_3833,c_5255,c_5621,c_8493,c_8492,c_8503,c_8502,c_13960,c_14984])).

cnf(c_15670,plain,
    ( sP0(sK9,sK11,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_9319,c_15665])).

cnf(c_1039,plain,
    ( sP0(sK9,sK11,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1038])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15670,c_1039])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:20:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.70/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/0.98  
% 3.70/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/0.98  
% 3.70/0.98  ------  iProver source info
% 3.70/0.98  
% 3.70/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.70/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/0.98  git: non_committed_changes: false
% 3.70/0.98  git: last_make_outside_of_git: false
% 3.70/0.98  
% 3.70/0.98  ------ 
% 3.70/0.98  
% 3.70/0.98  ------ Input Options
% 3.70/0.98  
% 3.70/0.98  --out_options                           all
% 3.70/0.98  --tptp_safe_out                         true
% 3.70/0.98  --problem_path                          ""
% 3.70/0.98  --include_path                          ""
% 3.70/0.98  --clausifier                            res/vclausify_rel
% 3.70/0.98  --clausifier_options                    --mode clausify
% 3.70/0.98  --stdin                                 false
% 3.70/0.98  --stats_out                             all
% 3.70/0.98  
% 3.70/0.98  ------ General Options
% 3.70/0.98  
% 3.70/0.98  --fof                                   false
% 3.70/0.98  --time_out_real                         305.
% 3.70/0.98  --time_out_virtual                      -1.
% 3.70/0.98  --symbol_type_check                     false
% 3.70/0.98  --clausify_out                          false
% 3.70/0.98  --sig_cnt_out                           false
% 3.70/0.98  --trig_cnt_out                          false
% 3.70/0.98  --trig_cnt_out_tolerance                1.
% 3.70/0.98  --trig_cnt_out_sk_spl                   false
% 3.70/0.98  --abstr_cl_out                          false
% 3.70/0.98  
% 3.70/0.98  ------ Global Options
% 3.70/0.98  
% 3.70/0.98  --schedule                              default
% 3.70/0.98  --add_important_lit                     false
% 3.70/0.98  --prop_solver_per_cl                    1000
% 3.70/0.98  --min_unsat_core                        false
% 3.70/0.98  --soft_assumptions                      false
% 3.70/0.98  --soft_lemma_size                       3
% 3.70/0.98  --prop_impl_unit_size                   0
% 3.70/0.98  --prop_impl_unit                        []
% 3.70/0.98  --share_sel_clauses                     true
% 3.70/0.98  --reset_solvers                         false
% 3.70/0.98  --bc_imp_inh                            [conj_cone]
% 3.70/0.98  --conj_cone_tolerance                   3.
% 3.70/0.98  --extra_neg_conj                        none
% 3.70/0.98  --large_theory_mode                     true
% 3.70/0.98  --prolific_symb_bound                   200
% 3.70/0.98  --lt_threshold                          2000
% 3.70/0.98  --clause_weak_htbl                      true
% 3.70/0.98  --gc_record_bc_elim                     false
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing Options
% 3.70/0.98  
% 3.70/0.98  --preprocessing_flag                    true
% 3.70/0.98  --time_out_prep_mult                    0.1
% 3.70/0.98  --splitting_mode                        input
% 3.70/0.98  --splitting_grd                         true
% 3.70/0.98  --splitting_cvd                         false
% 3.70/0.98  --splitting_cvd_svl                     false
% 3.70/0.98  --splitting_nvd                         32
% 3.70/0.98  --sub_typing                            true
% 3.70/0.98  --prep_gs_sim                           true
% 3.70/0.98  --prep_unflatten                        true
% 3.70/0.98  --prep_res_sim                          true
% 3.70/0.98  --prep_upred                            true
% 3.70/0.98  --prep_sem_filter                       exhaustive
% 3.70/0.98  --prep_sem_filter_out                   false
% 3.70/0.98  --pred_elim                             true
% 3.70/0.98  --res_sim_input                         true
% 3.70/0.98  --eq_ax_congr_red                       true
% 3.70/0.98  --pure_diseq_elim                       true
% 3.70/0.98  --brand_transform                       false
% 3.70/0.98  --non_eq_to_eq                          false
% 3.70/0.98  --prep_def_merge                        true
% 3.70/0.98  --prep_def_merge_prop_impl              false
% 3.70/0.98  --prep_def_merge_mbd                    true
% 3.70/0.98  --prep_def_merge_tr_red                 false
% 3.70/0.98  --prep_def_merge_tr_cl                  false
% 3.70/0.98  --smt_preprocessing                     true
% 3.70/0.98  --smt_ac_axioms                         fast
% 3.70/0.98  --preprocessed_out                      false
% 3.70/0.98  --preprocessed_stats                    false
% 3.70/0.98  
% 3.70/0.98  ------ Abstraction refinement Options
% 3.70/0.98  
% 3.70/0.98  --abstr_ref                             []
% 3.70/0.98  --abstr_ref_prep                        false
% 3.70/0.98  --abstr_ref_until_sat                   false
% 3.70/0.98  --abstr_ref_sig_restrict                funpre
% 3.70/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/0.98  --abstr_ref_under                       []
% 3.70/0.98  
% 3.70/0.98  ------ SAT Options
% 3.70/0.98  
% 3.70/0.98  --sat_mode                              false
% 3.70/0.98  --sat_fm_restart_options                ""
% 3.70/0.98  --sat_gr_def                            false
% 3.70/0.98  --sat_epr_types                         true
% 3.70/0.98  --sat_non_cyclic_types                  false
% 3.70/0.98  --sat_finite_models                     false
% 3.70/0.98  --sat_fm_lemmas                         false
% 3.70/0.98  --sat_fm_prep                           false
% 3.70/0.98  --sat_fm_uc_incr                        true
% 3.70/0.98  --sat_out_model                         small
% 3.70/0.98  --sat_out_clauses                       false
% 3.70/0.98  
% 3.70/0.98  ------ QBF Options
% 3.70/0.98  
% 3.70/0.98  --qbf_mode                              false
% 3.70/0.98  --qbf_elim_univ                         false
% 3.70/0.98  --qbf_dom_inst                          none
% 3.70/0.98  --qbf_dom_pre_inst                      false
% 3.70/0.98  --qbf_sk_in                             false
% 3.70/0.98  --qbf_pred_elim                         true
% 3.70/0.98  --qbf_split                             512
% 3.70/0.98  
% 3.70/0.98  ------ BMC1 Options
% 3.70/0.98  
% 3.70/0.98  --bmc1_incremental                      false
% 3.70/0.98  --bmc1_axioms                           reachable_all
% 3.70/0.98  --bmc1_min_bound                        0
% 3.70/0.98  --bmc1_max_bound                        -1
% 3.70/0.98  --bmc1_max_bound_default                -1
% 3.70/0.98  --bmc1_symbol_reachability              true
% 3.70/0.98  --bmc1_property_lemmas                  false
% 3.70/0.98  --bmc1_k_induction                      false
% 3.70/0.98  --bmc1_non_equiv_states                 false
% 3.70/0.98  --bmc1_deadlock                         false
% 3.70/0.98  --bmc1_ucm                              false
% 3.70/0.98  --bmc1_add_unsat_core                   none
% 3.70/0.98  --bmc1_unsat_core_children              false
% 3.70/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/0.98  --bmc1_out_stat                         full
% 3.70/0.98  --bmc1_ground_init                      false
% 3.70/0.98  --bmc1_pre_inst_next_state              false
% 3.70/0.98  --bmc1_pre_inst_state                   false
% 3.70/0.98  --bmc1_pre_inst_reach_state             false
% 3.70/0.98  --bmc1_out_unsat_core                   false
% 3.70/0.98  --bmc1_aig_witness_out                  false
% 3.70/0.98  --bmc1_verbose                          false
% 3.70/0.98  --bmc1_dump_clauses_tptp                false
% 3.70/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.70/0.98  --bmc1_dump_file                        -
% 3.70/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.70/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.70/0.98  --bmc1_ucm_extend_mode                  1
% 3.70/0.98  --bmc1_ucm_init_mode                    2
% 3.70/0.98  --bmc1_ucm_cone_mode                    none
% 3.70/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.70/0.98  --bmc1_ucm_relax_model                  4
% 3.70/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.70/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/0.98  --bmc1_ucm_layered_model                none
% 3.70/0.98  --bmc1_ucm_max_lemma_size               10
% 3.70/0.98  
% 3.70/0.98  ------ AIG Options
% 3.70/0.98  
% 3.70/0.98  --aig_mode                              false
% 3.70/0.98  
% 3.70/0.98  ------ Instantiation Options
% 3.70/0.98  
% 3.70/0.98  --instantiation_flag                    true
% 3.70/0.98  --inst_sos_flag                         false
% 3.70/0.98  --inst_sos_phase                        true
% 3.70/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/0.98  --inst_lit_sel_side                     num_symb
% 3.70/0.98  --inst_solver_per_active                1400
% 3.70/0.98  --inst_solver_calls_frac                1.
% 3.70/0.98  --inst_passive_queue_type               priority_queues
% 3.70/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/0.98  --inst_passive_queues_freq              [25;2]
% 3.70/0.98  --inst_dismatching                      true
% 3.70/0.98  --inst_eager_unprocessed_to_passive     true
% 3.70/0.98  --inst_prop_sim_given                   true
% 3.70/0.98  --inst_prop_sim_new                     false
% 3.70/0.98  --inst_subs_new                         false
% 3.70/0.98  --inst_eq_res_simp                      false
% 3.70/0.98  --inst_subs_given                       false
% 3.70/0.98  --inst_orphan_elimination               true
% 3.70/0.98  --inst_learning_loop_flag               true
% 3.70/0.98  --inst_learning_start                   3000
% 3.70/0.98  --inst_learning_factor                  2
% 3.70/0.98  --inst_start_prop_sim_after_learn       3
% 3.70/0.98  --inst_sel_renew                        solver
% 3.70/0.98  --inst_lit_activity_flag                true
% 3.70/0.98  --inst_restr_to_given                   false
% 3.70/0.98  --inst_activity_threshold               500
% 3.70/0.98  --inst_out_proof                        true
% 3.70/0.98  
% 3.70/0.98  ------ Resolution Options
% 3.70/0.98  
% 3.70/0.98  --resolution_flag                       true
% 3.70/0.98  --res_lit_sel                           adaptive
% 3.70/0.98  --res_lit_sel_side                      none
% 3.70/0.98  --res_ordering                          kbo
% 3.70/0.98  --res_to_prop_solver                    active
% 3.70/0.98  --res_prop_simpl_new                    false
% 3.70/0.98  --res_prop_simpl_given                  true
% 3.70/0.98  --res_passive_queue_type                priority_queues
% 3.70/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/0.98  --res_passive_queues_freq               [15;5]
% 3.70/0.98  --res_forward_subs                      full
% 3.70/0.98  --res_backward_subs                     full
% 3.70/0.98  --res_forward_subs_resolution           true
% 3.70/0.98  --res_backward_subs_resolution          true
% 3.70/0.98  --res_orphan_elimination                true
% 3.70/0.98  --res_time_limit                        2.
% 3.70/0.98  --res_out_proof                         true
% 3.70/0.98  
% 3.70/0.98  ------ Superposition Options
% 3.70/0.98  
% 3.70/0.98  --superposition_flag                    true
% 3.70/0.98  --sup_passive_queue_type                priority_queues
% 3.70/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.70/0.98  --demod_completeness_check              fast
% 3.70/0.98  --demod_use_ground                      true
% 3.70/0.98  --sup_to_prop_solver                    passive
% 3.70/0.98  --sup_prop_simpl_new                    true
% 3.70/0.98  --sup_prop_simpl_given                  true
% 3.70/0.98  --sup_fun_splitting                     false
% 3.70/0.98  --sup_smt_interval                      50000
% 3.70/0.98  
% 3.70/0.98  ------ Superposition Simplification Setup
% 3.70/0.98  
% 3.70/0.98  --sup_indices_passive                   []
% 3.70/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.98  --sup_full_bw                           [BwDemod]
% 3.70/0.98  --sup_immed_triv                        [TrivRules]
% 3.70/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.98  --sup_immed_bw_main                     []
% 3.70/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/0.98  
% 3.70/0.98  ------ Combination Options
% 3.70/0.98  
% 3.70/0.98  --comb_res_mult                         3
% 3.70/0.98  --comb_sup_mult                         2
% 3.70/0.98  --comb_inst_mult                        10
% 3.70/0.98  
% 3.70/0.98  ------ Debug Options
% 3.70/0.98  
% 3.70/0.98  --dbg_backtrace                         false
% 3.70/0.98  --dbg_dump_prop_clauses                 false
% 3.70/0.98  --dbg_dump_prop_clauses_file            -
% 3.70/0.98  --dbg_out_stat                          false
% 3.70/0.98  ------ Parsing...
% 3.70/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.98  ------ Proving...
% 3.70/0.98  ------ Problem Properties 
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  clauses                                 25
% 3.70/0.98  conjectures                             9
% 3.70/0.98  EPR                                     8
% 3.70/0.98  Horn                                    18
% 3.70/0.98  unary                                   11
% 3.70/0.98  binary                                  10
% 3.70/0.98  lits                                    53
% 3.70/0.98  lits eq                                 12
% 3.70/0.98  fd_pure                                 0
% 3.70/0.98  fd_pseudo                               0
% 3.70/0.98  fd_cond                                 0
% 3.70/0.98  fd_pseudo_cond                          2
% 3.70/0.98  AC symbols                              0
% 3.70/0.98  
% 3.70/0.98  ------ Schedule dynamic 5 is on 
% 3.70/0.98  
% 3.70/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ 
% 3.70/0.98  Current options:
% 3.70/0.98  ------ 
% 3.70/0.98  
% 3.70/0.98  ------ Input Options
% 3.70/0.98  
% 3.70/0.98  --out_options                           all
% 3.70/0.98  --tptp_safe_out                         true
% 3.70/0.98  --problem_path                          ""
% 3.70/0.98  --include_path                          ""
% 3.70/0.98  --clausifier                            res/vclausify_rel
% 3.70/0.98  --clausifier_options                    --mode clausify
% 3.70/0.98  --stdin                                 false
% 3.70/0.98  --stats_out                             all
% 3.70/0.98  
% 3.70/0.98  ------ General Options
% 3.70/0.98  
% 3.70/0.98  --fof                                   false
% 3.70/0.98  --time_out_real                         305.
% 3.70/0.98  --time_out_virtual                      -1.
% 3.70/0.98  --symbol_type_check                     false
% 3.70/0.98  --clausify_out                          false
% 3.70/0.98  --sig_cnt_out                           false
% 3.70/0.98  --trig_cnt_out                          false
% 3.70/0.98  --trig_cnt_out_tolerance                1.
% 3.70/0.98  --trig_cnt_out_sk_spl                   false
% 3.70/0.98  --abstr_cl_out                          false
% 3.70/0.98  
% 3.70/0.98  ------ Global Options
% 3.70/0.98  
% 3.70/0.98  --schedule                              default
% 3.70/0.98  --add_important_lit                     false
% 3.70/0.98  --prop_solver_per_cl                    1000
% 3.70/0.98  --min_unsat_core                        false
% 3.70/0.98  --soft_assumptions                      false
% 3.70/0.98  --soft_lemma_size                       3
% 3.70/0.98  --prop_impl_unit_size                   0
% 3.70/0.98  --prop_impl_unit                        []
% 3.70/0.98  --share_sel_clauses                     true
% 3.70/0.98  --reset_solvers                         false
% 3.70/0.98  --bc_imp_inh                            [conj_cone]
% 3.70/0.98  --conj_cone_tolerance                   3.
% 3.70/0.98  --extra_neg_conj                        none
% 3.70/0.98  --large_theory_mode                     true
% 3.70/0.98  --prolific_symb_bound                   200
% 3.70/0.98  --lt_threshold                          2000
% 3.70/0.98  --clause_weak_htbl                      true
% 3.70/0.98  --gc_record_bc_elim                     false
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing Options
% 3.70/0.98  
% 3.70/0.98  --preprocessing_flag                    true
% 3.70/0.98  --time_out_prep_mult                    0.1
% 3.70/0.98  --splitting_mode                        input
% 3.70/0.98  --splitting_grd                         true
% 3.70/0.98  --splitting_cvd                         false
% 3.70/0.98  --splitting_cvd_svl                     false
% 3.70/0.98  --splitting_nvd                         32
% 3.70/0.98  --sub_typing                            true
% 3.70/0.98  --prep_gs_sim                           true
% 3.70/0.98  --prep_unflatten                        true
% 3.70/0.98  --prep_res_sim                          true
% 3.70/0.98  --prep_upred                            true
% 3.70/0.98  --prep_sem_filter                       exhaustive
% 3.70/0.98  --prep_sem_filter_out                   false
% 3.70/0.98  --pred_elim                             true
% 3.70/0.98  --res_sim_input                         true
% 3.70/0.98  --eq_ax_congr_red                       true
% 3.70/0.98  --pure_diseq_elim                       true
% 3.70/0.98  --brand_transform                       false
% 3.70/0.98  --non_eq_to_eq                          false
% 3.70/0.98  --prep_def_merge                        true
% 3.70/0.98  --prep_def_merge_prop_impl              false
% 3.70/0.98  --prep_def_merge_mbd                    true
% 3.70/0.98  --prep_def_merge_tr_red                 false
% 3.70/0.98  --prep_def_merge_tr_cl                  false
% 3.70/0.98  --smt_preprocessing                     true
% 3.70/0.98  --smt_ac_axioms                         fast
% 3.70/0.98  --preprocessed_out                      false
% 3.70/0.98  --preprocessed_stats                    false
% 3.70/0.98  
% 3.70/0.98  ------ Abstraction refinement Options
% 3.70/0.98  
% 3.70/0.98  --abstr_ref                             []
% 3.70/0.98  --abstr_ref_prep                        false
% 3.70/0.98  --abstr_ref_until_sat                   false
% 3.70/0.98  --abstr_ref_sig_restrict                funpre
% 3.70/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/0.98  --abstr_ref_under                       []
% 3.70/0.98  
% 3.70/0.98  ------ SAT Options
% 3.70/0.98  
% 3.70/0.98  --sat_mode                              false
% 3.70/0.98  --sat_fm_restart_options                ""
% 3.70/0.98  --sat_gr_def                            false
% 3.70/0.98  --sat_epr_types                         true
% 3.70/0.98  --sat_non_cyclic_types                  false
% 3.70/0.98  --sat_finite_models                     false
% 3.70/0.98  --sat_fm_lemmas                         false
% 3.70/0.98  --sat_fm_prep                           false
% 3.70/0.98  --sat_fm_uc_incr                        true
% 3.70/0.98  --sat_out_model                         small
% 3.70/0.98  --sat_out_clauses                       false
% 3.70/0.98  
% 3.70/0.98  ------ QBF Options
% 3.70/0.98  
% 3.70/0.98  --qbf_mode                              false
% 3.70/0.98  --qbf_elim_univ                         false
% 3.70/0.98  --qbf_dom_inst                          none
% 3.70/0.98  --qbf_dom_pre_inst                      false
% 3.70/0.98  --qbf_sk_in                             false
% 3.70/0.98  --qbf_pred_elim                         true
% 3.70/0.98  --qbf_split                             512
% 3.70/0.98  
% 3.70/0.98  ------ BMC1 Options
% 3.70/0.98  
% 3.70/0.98  --bmc1_incremental                      false
% 3.70/0.98  --bmc1_axioms                           reachable_all
% 3.70/0.98  --bmc1_min_bound                        0
% 3.70/0.98  --bmc1_max_bound                        -1
% 3.70/0.98  --bmc1_max_bound_default                -1
% 3.70/0.98  --bmc1_symbol_reachability              true
% 3.70/0.98  --bmc1_property_lemmas                  false
% 3.70/0.98  --bmc1_k_induction                      false
% 3.70/0.98  --bmc1_non_equiv_states                 false
% 3.70/0.98  --bmc1_deadlock                         false
% 3.70/0.98  --bmc1_ucm                              false
% 3.70/0.98  --bmc1_add_unsat_core                   none
% 3.70/0.98  --bmc1_unsat_core_children              false
% 3.70/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/0.98  --bmc1_out_stat                         full
% 3.70/0.98  --bmc1_ground_init                      false
% 3.70/0.98  --bmc1_pre_inst_next_state              false
% 3.70/0.98  --bmc1_pre_inst_state                   false
% 3.70/0.98  --bmc1_pre_inst_reach_state             false
% 3.70/0.98  --bmc1_out_unsat_core                   false
% 3.70/0.98  --bmc1_aig_witness_out                  false
% 3.70/0.98  --bmc1_verbose                          false
% 3.70/0.98  --bmc1_dump_clauses_tptp                false
% 3.70/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.70/0.98  --bmc1_dump_file                        -
% 3.70/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.70/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.70/0.98  --bmc1_ucm_extend_mode                  1
% 3.70/0.98  --bmc1_ucm_init_mode                    2
% 3.70/0.98  --bmc1_ucm_cone_mode                    none
% 3.70/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.70/0.98  --bmc1_ucm_relax_model                  4
% 3.70/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.70/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/0.98  --bmc1_ucm_layered_model                none
% 3.70/0.98  --bmc1_ucm_max_lemma_size               10
% 3.70/0.98  
% 3.70/0.98  ------ AIG Options
% 3.70/0.98  
% 3.70/0.98  --aig_mode                              false
% 3.70/0.98  
% 3.70/0.98  ------ Instantiation Options
% 3.70/0.98  
% 3.70/0.98  --instantiation_flag                    true
% 3.70/0.98  --inst_sos_flag                         false
% 3.70/0.98  --inst_sos_phase                        true
% 3.70/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/0.98  --inst_lit_sel_side                     none
% 3.70/0.98  --inst_solver_per_active                1400
% 3.70/0.98  --inst_solver_calls_frac                1.
% 3.70/0.98  --inst_passive_queue_type               priority_queues
% 3.70/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/0.98  --inst_passive_queues_freq              [25;2]
% 3.70/0.98  --inst_dismatching                      true
% 3.70/0.98  --inst_eager_unprocessed_to_passive     true
% 3.70/0.98  --inst_prop_sim_given                   true
% 3.70/0.98  --inst_prop_sim_new                     false
% 3.70/0.98  --inst_subs_new                         false
% 3.70/0.98  --inst_eq_res_simp                      false
% 3.70/0.98  --inst_subs_given                       false
% 3.70/0.98  --inst_orphan_elimination               true
% 3.70/0.98  --inst_learning_loop_flag               true
% 3.70/0.98  --inst_learning_start                   3000
% 3.70/0.98  --inst_learning_factor                  2
% 3.70/0.98  --inst_start_prop_sim_after_learn       3
% 3.70/0.98  --inst_sel_renew                        solver
% 3.70/0.98  --inst_lit_activity_flag                true
% 3.70/0.98  --inst_restr_to_given                   false
% 3.70/0.98  --inst_activity_threshold               500
% 3.70/0.98  --inst_out_proof                        true
% 3.70/0.98  
% 3.70/0.98  ------ Resolution Options
% 3.70/0.98  
% 3.70/0.98  --resolution_flag                       false
% 3.70/0.98  --res_lit_sel                           adaptive
% 3.70/0.98  --res_lit_sel_side                      none
% 3.70/0.98  --res_ordering                          kbo
% 3.70/0.98  --res_to_prop_solver                    active
% 3.70/0.98  --res_prop_simpl_new                    false
% 3.70/0.98  --res_prop_simpl_given                  true
% 3.70/0.98  --res_passive_queue_type                priority_queues
% 3.70/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/0.98  --res_passive_queues_freq               [15;5]
% 3.70/0.98  --res_forward_subs                      full
% 3.70/0.98  --res_backward_subs                     full
% 3.70/0.98  --res_forward_subs_resolution           true
% 3.70/0.98  --res_backward_subs_resolution          true
% 3.70/0.98  --res_orphan_elimination                true
% 3.70/0.98  --res_time_limit                        2.
% 3.70/0.98  --res_out_proof                         true
% 3.70/0.98  
% 3.70/0.98  ------ Superposition Options
% 3.70/0.98  
% 3.70/0.98  --superposition_flag                    true
% 3.70/0.98  --sup_passive_queue_type                priority_queues
% 3.70/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.70/0.98  --demod_completeness_check              fast
% 3.70/0.98  --demod_use_ground                      true
% 3.70/0.98  --sup_to_prop_solver                    passive
% 3.70/0.98  --sup_prop_simpl_new                    true
% 3.70/0.98  --sup_prop_simpl_given                  true
% 3.70/0.98  --sup_fun_splitting                     false
% 3.70/0.98  --sup_smt_interval                      50000
% 3.70/0.98  
% 3.70/0.98  ------ Superposition Simplification Setup
% 3.70/0.98  
% 3.70/0.98  --sup_indices_passive                   []
% 3.70/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.98  --sup_full_bw                           [BwDemod]
% 3.70/0.98  --sup_immed_triv                        [TrivRules]
% 3.70/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.98  --sup_immed_bw_main                     []
% 3.70/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/0.98  
% 3.70/0.98  ------ Combination Options
% 3.70/0.98  
% 3.70/0.98  --comb_res_mult                         3
% 3.70/0.98  --comb_sup_mult                         2
% 3.70/0.98  --comb_inst_mult                        10
% 3.70/0.98  
% 3.70/0.98  ------ Debug Options
% 3.70/0.98  
% 3.70/0.98  --dbg_backtrace                         false
% 3.70/0.98  --dbg_dump_prop_clauses                 false
% 3.70/0.98  --dbg_dump_prop_clauses_file            -
% 3.70/0.98  --dbg_out_stat                          false
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  ------ Proving...
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  % SZS status Theorem for theBenchmark.p
% 3.70/0.98  
% 3.70/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/0.98  
% 3.70/0.98  fof(f16,plain,(
% 3.70/0.98    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 3.70/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.70/0.98  
% 3.70/0.98  fof(f21,plain,(
% 3.70/0.98    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X5,X6) & k1_funct_1(X2,X4) = X6 & k1_funct_1(X2,X3) = X5 & m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X2,X0)))),
% 3.70/0.98    inference(nnf_transformation,[],[f16])).
% 3.70/0.98  
% 3.70/0.98  fof(f22,plain,(
% 3.70/0.98    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,X3,X4) & m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X2)))) & (! [X7] : (! [X8] : (! [X9] : (! [X10] : (r1_orders_2(X0,X9,X10) | k1_funct_1(X1,X8) != X10 | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X0))) | ~m1_subset_1(X9,u1_struct_0(X0))) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~sP0(X0,X1,X2)))),
% 3.70/0.98    inference(rectify,[],[f21])).
% 3.70/0.98  
% 3.70/0.98  fof(f26,plain,(
% 3.70/0.98    ( ! [X4,X5,X3] : (! [X2,X1,X0] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) => (~r1_orders_2(X0,X5,sK5(X0,X1,X2)) & k1_funct_1(X1,X4) = sK5(X0,X1,X2) & k1_funct_1(X1,X3) = X5 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))) )),
% 3.70/0.98    introduced(choice_axiom,[])).
% 3.70/0.98  
% 3.70/0.98  fof(f25,plain,(
% 3.70/0.98    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) => (? [X6] : (~r1_orders_2(X0,sK4(X0,X1,X2),X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = sK4(X0,X1,X2) & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))) )),
% 3.70/0.98    introduced(choice_axiom,[])).
% 3.70/0.98  
% 3.70/0.98  fof(f24,plain,(
% 3.70/0.98    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,X3,X4) & m1_subset_1(X4,u1_struct_0(X2))) => (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,sK3(X0,X1,X2)) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,X3,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2))))) )),
% 3.70/0.98    introduced(choice_axiom,[])).
% 3.70/0.98  
% 3.70/0.98  fof(f23,plain,(
% 3.70/0.98    ! [X2,X1,X0] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,X3,X4) & m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X2))) => (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,sK2(X0,X1,X2)) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,sK2(X0,X1,X2),X4) & m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2))))),
% 3.70/0.98    introduced(choice_axiom,[])).
% 3.70/0.98  
% 3.70/0.98  fof(f27,plain,(
% 3.70/0.98    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((((~r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2)) & k1_funct_1(X1,sK3(X0,X1,X2)) = sK5(X0,X1,X2) & k1_funct_1(X1,sK2(X0,X1,X2)) = sK4(X0,X1,X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) & r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)))) & (! [X7] : (! [X8] : (! [X9] : (! [X10] : (r1_orders_2(X0,X9,X10) | k1_funct_1(X1,X8) != X10 | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X0))) | ~m1_subset_1(X9,u1_struct_0(X0))) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~sP0(X0,X1,X2)))),
% 3.70/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f26,f25,f24,f23])).
% 3.70/0.98  
% 3.70/0.98  fof(f45,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2))) )),
% 3.70/0.98    inference(cnf_transformation,[],[f27])).
% 3.70/0.98  
% 3.70/0.98  fof(f44,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2))) )),
% 3.70/0.98    inference(cnf_transformation,[],[f27])).
% 3.70/0.98  
% 3.70/0.98  fof(f5,conjecture,(
% 3.70/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((l1_orders_2(X2) & ~v2_struct_0(X2)) => ! [X3] : ((l1_orders_2(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 3.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f6,negated_conjecture,(
% 3.70/0.98    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((l1_orders_2(X2) & ~v2_struct_0(X2)) => ! [X3] : ((l1_orders_2(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 3.70/0.98    inference(negated_conjecture,[],[f5])).
% 3.70/0.98  
% 3.70/0.98  fof(f7,plain,(
% 3.70/0.98    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : (l1_orders_2(X2) => ! [X3] : (l1_orders_2(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 3.70/0.98    inference(pure_predicate_removal,[],[f6])).
% 3.70/0.98  
% 3.70/0.98  fof(f14,plain,(
% 3.70/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~v5_orders_3(X5,X2,X3) & (v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 3.70/0.98    inference(ennf_transformation,[],[f7])).
% 3.70/0.98  
% 3.70/0.98  fof(f15,plain,(
% 3.70/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 3.70/0.98    inference(flattening,[],[f14])).
% 3.70/0.98  
% 3.70/0.98  fof(f33,plain,(
% 3.70/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => (~v5_orders_3(sK11,X2,X3) & v5_orders_3(X4,X0,X1) & sK11 = X4 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(sK11,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(sK11))) )),
% 3.70/0.98    introduced(choice_axiom,[])).
% 3.70/0.98  
% 3.70/0.98  fof(f32,plain,(
% 3.70/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(sK10,X0,X1) & sK10 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK10,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK10))) )),
% 3.70/0.98    introduced(choice_axiom,[])).
% 3.70/0.98  
% 3.70/0.98  fof(f31,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) => (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,sK9) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK9)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK9)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(sK9))) )),
% 3.70/0.98    introduced(choice_axiom,[])).
% 3.70/0.98  
% 3.70/0.98  fof(f30,plain,(
% 3.70/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) => (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,sK8,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(sK8))) )),
% 3.70/0.98    introduced(choice_axiom,[])).
% 3.70/0.98  
% 3.70/0.98  fof(f29,plain,(
% 3.70/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,sK7) & X4 = X5 & g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK7)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(sK7))) )),
% 3.70/0.98    introduced(choice_axiom,[])).
% 3.70/0.98  
% 3.70/0.98  fof(f28,plain,(
% 3.70/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,sK6,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(sK6))),
% 3.70/0.98    introduced(choice_axiom,[])).
% 3.70/0.98  
% 3.70/0.98  fof(f34,plain,(
% 3.70/0.98    (((((~v5_orders_3(sK11,sK8,sK9) & v5_orders_3(sK10,sK6,sK7) & sK10 = sK11 & g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) & g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) & v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) & v1_funct_1(sK11)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(sK10)) & l1_orders_2(sK9)) & l1_orders_2(sK8)) & l1_orders_2(sK7)) & l1_orders_2(sK6)),
% 3.70/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f15,f33,f32,f31,f30,f29,f28])).
% 3.70/0.98  
% 3.70/0.98  fof(f62,plain,(
% 3.70/0.98    g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8))),
% 3.70/0.98    inference(cnf_transformation,[],[f34])).
% 3.70/0.98  
% 3.70/0.98  fof(f2,axiom,(
% 3.70/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f9,plain,(
% 3.70/0.98    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.70/0.98    inference(ennf_transformation,[],[f2])).
% 3.70/0.98  
% 3.70/0.98  fof(f36,plain,(
% 3.70/0.98    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.70/0.98    inference(cnf_transformation,[],[f9])).
% 3.70/0.98  
% 3.70/0.98  fof(f52,plain,(
% 3.70/0.98    l1_orders_2(sK6)),
% 3.70/0.98    inference(cnf_transformation,[],[f34])).
% 3.70/0.98  
% 3.70/0.98  fof(f1,axiom,(
% 3.70/0.98    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 3.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f8,plain,(
% 3.70/0.98    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.70/0.98    inference(ennf_transformation,[],[f1])).
% 3.70/0.98  
% 3.70/0.98  fof(f35,plain,(
% 3.70/0.98    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f8])).
% 3.70/0.98  
% 3.70/0.98  fof(f3,axiom,(
% 3.70/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((X3 = X5 & X2 = X4) => ((r2_orders_2(X0,X2,X3) => r2_orders_2(X1,X4,X5)) & (r1_orders_2(X0,X2,X3) => r1_orders_2(X1,X4,X5)))))))))))),
% 3.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f10,plain,(
% 3.70/0.98    ! [X0] : (! [X1] : ((! [X2] : (! [X3] : (! [X4] : (! [X5] : ((((r2_orders_2(X1,X4,X5) | ~r2_orders_2(X0,X2,X3)) & (r1_orders_2(X1,X4,X5) | ~r1_orders_2(X0,X2,X3))) | (X3 != X5 | X2 != X4)) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 3.70/0.98    inference(ennf_transformation,[],[f3])).
% 3.70/0.98  
% 3.70/0.98  fof(f11,plain,(
% 3.70/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r2_orders_2(X1,X4,X5) | ~r2_orders_2(X0,X2,X3)) & (r1_orders_2(X1,X4,X5) | ~r1_orders_2(X0,X2,X3))) | X3 != X5 | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 3.70/0.98    inference(flattening,[],[f10])).
% 3.70/0.98  
% 3.70/0.98  fof(f38,plain,(
% 3.70/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (r1_orders_2(X1,X4,X5) | ~r1_orders_2(X0,X2,X3) | X3 != X5 | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f11])).
% 3.70/0.98  
% 3.70/0.98  fof(f69,plain,(
% 3.70/0.98    ( ! [X4,X2,X0,X5,X1] : (r1_orders_2(X1,X4,X5) | ~r1_orders_2(X0,X2,X5) | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 3.70/0.98    inference(equality_resolution,[],[f38])).
% 3.70/0.98  
% 3.70/0.98  fof(f70,plain,(
% 3.70/0.98    ( ! [X4,X0,X5,X1] : (r1_orders_2(X1,X4,X5) | ~r1_orders_2(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 3.70/0.98    inference(equality_resolution,[],[f69])).
% 3.70/0.98  
% 3.70/0.98  fof(f54,plain,(
% 3.70/0.98    l1_orders_2(sK8)),
% 3.70/0.98    inference(cnf_transformation,[],[f34])).
% 3.70/0.98  
% 3.70/0.98  fof(f43,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2))) )),
% 3.70/0.98    inference(cnf_transformation,[],[f27])).
% 3.70/0.98  
% 3.70/0.98  fof(f48,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | k1_funct_1(X1,sK2(X0,X1,X2)) = sK4(X0,X1,X2)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f27])).
% 3.70/0.98  
% 3.70/0.98  fof(f17,plain,(
% 3.70/0.98    ! [X0,X2,X1] : ((v5_orders_3(X2,X0,X1) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 3.70/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.70/0.98  
% 3.70/0.98  fof(f19,plain,(
% 3.70/0.98    ! [X0,X2,X1] : (((v5_orders_3(X2,X0,X1) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~v5_orders_3(X2,X0,X1))) | ~sP1(X0,X2,X1))),
% 3.70/0.98    inference(nnf_transformation,[],[f17])).
% 3.70/0.98  
% 3.70/0.98  fof(f20,plain,(
% 3.70/0.98    ! [X0,X1,X2] : (((v5_orders_3(X1,X0,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v5_orders_3(X1,X0,X2))) | ~sP1(X0,X1,X2))),
% 3.70/0.98    inference(rectify,[],[f19])).
% 3.70/0.98  
% 3.70/0.98  fof(f41,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (v5_orders_3(X1,X0,X2) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f20])).
% 3.70/0.98  
% 3.70/0.98  fof(f66,plain,(
% 3.70/0.98    ~v5_orders_3(sK11,sK8,sK9)),
% 3.70/0.98    inference(cnf_transformation,[],[f34])).
% 3.70/0.98  
% 3.70/0.98  fof(f4,axiom,(
% 3.70/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_orders_3(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_orders_2(X0,X3,X4) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X1)) => ((k1_funct_1(X2,X4) = X6 & k1_funct_1(X2,X3) = X5) => r1_orders_2(X1,X5,X6)))))))))))),
% 3.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.98  
% 3.70/0.98  fof(f12,plain,(
% 3.70/0.98    ! [X0] : (! [X1] : (! [X2] : ((v5_orders_3(X2,X0,X1) <=> ! [X3] : (! [X4] : ((! [X5] : (! [X6] : ((r1_orders_2(X1,X5,X6) | (k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5)) | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 3.70/0.98    inference(ennf_transformation,[],[f4])).
% 3.70/0.98  
% 3.70/0.98  fof(f13,plain,(
% 3.70/0.98    ! [X0] : (! [X1] : (! [X2] : ((v5_orders_3(X2,X0,X1) <=> ! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 3.70/0.98    inference(flattening,[],[f12])).
% 3.70/0.98  
% 3.70/0.98  fof(f18,plain,(
% 3.70/0.98    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 3.70/0.98    inference(definition_folding,[],[f13,f17,f16])).
% 3.70/0.98  
% 3.70/0.98  fof(f51,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f18])).
% 3.70/0.98  
% 3.70/0.98  fof(f60,plain,(
% 3.70/0.98    v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9))),
% 3.70/0.98    inference(cnf_transformation,[],[f34])).
% 3.70/0.98  
% 3.70/0.98  fof(f59,plain,(
% 3.70/0.98    v1_funct_1(sK11)),
% 3.70/0.98    inference(cnf_transformation,[],[f34])).
% 3.70/0.98  
% 3.70/0.98  fof(f55,plain,(
% 3.70/0.98    l1_orders_2(sK9)),
% 3.70/0.98    inference(cnf_transformation,[],[f34])).
% 3.70/0.98  
% 3.70/0.98  fof(f61,plain,(
% 3.70/0.98    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))),
% 3.70/0.98    inference(cnf_transformation,[],[f34])).
% 3.70/0.98  
% 3.70/0.98  fof(f49,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | k1_funct_1(X1,sK3(X0,X1,X2)) = sK5(X0,X1,X2)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f27])).
% 3.70/0.98  
% 3.70/0.98  fof(f40,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | ~v5_orders_3(X1,X0,X2) | ~sP1(X0,X1,X2)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f20])).
% 3.70/0.98  
% 3.70/0.98  fof(f65,plain,(
% 3.70/0.98    v5_orders_3(sK10,sK6,sK7)),
% 3.70/0.98    inference(cnf_transformation,[],[f34])).
% 3.70/0.98  
% 3.70/0.98  fof(f53,plain,(
% 3.70/0.98    l1_orders_2(sK7)),
% 3.70/0.98    inference(cnf_transformation,[],[f34])).
% 3.70/0.98  
% 3.70/0.98  fof(f64,plain,(
% 3.70/0.98    sK10 = sK11),
% 3.70/0.98    inference(cnf_transformation,[],[f34])).
% 3.70/0.98  
% 3.70/0.98  fof(f57,plain,(
% 3.70/0.98    v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7))),
% 3.70/0.98    inference(cnf_transformation,[],[f34])).
% 3.70/0.98  
% 3.70/0.98  fof(f56,plain,(
% 3.70/0.98    v1_funct_1(sK10)),
% 3.70/0.98    inference(cnf_transformation,[],[f34])).
% 3.70/0.98  
% 3.70/0.98  fof(f58,plain,(
% 3.70/0.98    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))),
% 3.70/0.98    inference(cnf_transformation,[],[f34])).
% 3.70/0.98  
% 3.70/0.98  fof(f42,plain,(
% 3.70/0.98    ( ! [X2,X0,X10,X8,X7,X1,X9] : (r1_orders_2(X0,X9,X10) | k1_funct_1(X1,X8) != X10 | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X0)) | ~m1_subset_1(X9,u1_struct_0(X0)) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 3.70/0.98    inference(cnf_transformation,[],[f27])).
% 3.70/0.98  
% 3.70/0.98  fof(f71,plain,(
% 3.70/0.98    ( ! [X2,X0,X8,X7,X1,X9] : (r1_orders_2(X0,X9,k1_funct_1(X1,X8)) | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0)) | ~m1_subset_1(X9,u1_struct_0(X0)) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 3.70/0.98    inference(equality_resolution,[],[f42])).
% 3.70/0.98  
% 3.70/0.98  fof(f72,plain,(
% 3.70/0.98    ( ! [X2,X0,X8,X7,X1] : (r1_orders_2(X0,k1_funct_1(X1,X7),k1_funct_1(X1,X8)) | ~m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0)) | ~m1_subset_1(k1_funct_1(X1,X7),u1_struct_0(X0)) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 3.70/0.98    inference(equality_resolution,[],[f71])).
% 3.70/0.98  
% 3.70/0.98  fof(f63,plain,(
% 3.70/0.98    g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9))),
% 3.70/0.98    inference(cnf_transformation,[],[f34])).
% 3.70/0.98  
% 3.70/0.98  fof(f47,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) )),
% 3.70/0.98    inference(cnf_transformation,[],[f27])).
% 3.70/0.98  
% 3.70/0.98  fof(f46,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) )),
% 3.70/0.98    inference(cnf_transformation,[],[f27])).
% 3.70/0.98  
% 3.70/0.98  fof(f50,plain,(
% 3.70/0.98    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2))) )),
% 3.70/0.98    inference(cnf_transformation,[],[f27])).
% 3.70/0.98  
% 3.70/0.98  fof(f37,plain,(
% 3.70/0.98    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.70/0.98    inference(cnf_transformation,[],[f9])).
% 3.70/0.98  
% 3.70/0.98  cnf(c_12,plain,
% 3.70/0.98      ( sP0(X0,X1,X2) | r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2)) ),
% 3.70/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2388,plain,
% 3.70/0.98      ( sP0(X0,X1,X2) = iProver_top
% 3.70/0.98      | r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2)) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_13,plain,
% 3.70/0.98      ( sP0(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2)) ),
% 3.70/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2387,plain,
% 3.70/0.98      ( sP0(X0,X1,X2) = iProver_top
% 3.70/0.98      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2)) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_21,negated_conjecture,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) ),
% 3.70/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2,plain,
% 3.70/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.70/0.98      | X2 = X1
% 3.70/0.98      | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
% 3.70/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2395,plain,
% 3.70/0.98      ( X0 = X1
% 3.70/0.98      | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
% 3.70/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3127,plain,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
% 3.70/0.98      | u1_struct_0(sK6) = X0
% 3.70/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_21,c_2395]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_31,negated_conjecture,
% 3.70/0.98      ( l1_orders_2(sK6) ),
% 3.70/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_0,plain,
% 3.70/0.98      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.70/0.98      | ~ l1_orders_2(X0) ),
% 3.70/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_87,plain,
% 3.70/0.98      ( m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
% 3.70/0.98      | ~ l1_orders_2(sK6) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3129,plain,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
% 3.70/0.98      | u1_struct_0(sK6) = X0
% 3.70/0.98      | m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_21,c_2395]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3164,plain,
% 3.70/0.98      ( ~ m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
% 3.70/0.98      | g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
% 3.70/0.98      | u1_struct_0(sK6) = X0 ),
% 3.70/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3129]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3293,plain,
% 3.70/0.98      ( u1_struct_0(sK6) = X0
% 3.70/0.98      | g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1) ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_3127,c_31,c_87,c_3164]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3294,plain,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
% 3.70/0.98      | u1_struct_0(sK6) = X0 ),
% 3.70/0.98      inference(renaming,[status(thm)],[c_3293]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3300,plain,
% 3.70/0.98      ( u1_struct_0(sK8) = u1_struct_0(sK6) ),
% 3.70/0.98      inference(equality_resolution,[status(thm)],[c_3294]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_4,plain,
% 3.70/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 3.70/0.98      | r1_orders_2(X3,X1,X2)
% 3.70/0.98      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 3.70/0.98      | ~ m1_subset_1(X1,u1_struct_0(X3))
% 3.70/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.70/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.70/0.98      | ~ l1_orders_2(X0)
% 3.70/0.98      | ~ l1_orders_2(X3)
% 3.70/0.98      | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
% 3.70/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2394,plain,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
% 3.70/0.98      | r1_orders_2(X1,X2,X3) != iProver_top
% 3.70/0.98      | r1_orders_2(X0,X2,X3) = iProver_top
% 3.70/0.98      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.70/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.70/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.70/0.98      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.70/0.98      | l1_orders_2(X1) != iProver_top
% 3.70/0.98      | l1_orders_2(X0) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_4002,plain,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK6))
% 3.70/0.98      | r1_orders_2(X0,X1,X2) != iProver_top
% 3.70/0.98      | r1_orders_2(sK6,X1,X2) = iProver_top
% 3.70/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.70/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.70/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.70/0.98      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
% 3.70/0.98      | l1_orders_2(X0) != iProver_top
% 3.70/0.98      | l1_orders_2(sK6) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_3300,c_2394]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3593,plain,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) ),
% 3.70/0.98      inference(demodulation,[status(thm)],[c_3300,c_21]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_4053,plain,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8))
% 3.70/0.98      | r1_orders_2(X0,X1,X2) != iProver_top
% 3.70/0.98      | r1_orders_2(sK6,X1,X2) = iProver_top
% 3.70/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.70/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.70/0.98      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(X2,u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | l1_orders_2(X0) != iProver_top
% 3.70/0.98      | l1_orders_2(sK6) != iProver_top ),
% 3.70/0.98      inference(light_normalisation,[status(thm)],[c_4002,c_3300,c_3593]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_32,plain,
% 3.70/0.98      ( l1_orders_2(sK6) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_5064,plain,
% 3.70/0.98      ( l1_orders_2(X0) != iProver_top
% 3.70/0.98      | m1_subset_1(X2,u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.70/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.70/0.98      | r1_orders_2(sK6,X1,X2) = iProver_top
% 3.70/0.98      | r1_orders_2(X0,X1,X2) != iProver_top
% 3.70/0.98      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_4053,c_32]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_5065,plain,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8))
% 3.70/0.98      | r1_orders_2(X0,X1,X2) != iProver_top
% 3.70/0.98      | r1_orders_2(sK6,X1,X2) = iProver_top
% 3.70/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.70/0.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.70/0.98      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(X2,u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | l1_orders_2(X0) != iProver_top ),
% 3.70/0.98      inference(renaming,[status(thm)],[c_5064]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_5078,plain,
% 3.70/0.98      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.70/0.98      | r1_orders_2(sK8,X0,X1) != iProver_top
% 3.70/0.98      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | l1_orders_2(sK8) != iProver_top ),
% 3.70/0.98      inference(equality_resolution,[status(thm)],[c_5065]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_29,negated_conjecture,
% 3.70/0.98      ( l1_orders_2(sK8) ),
% 3.70/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_34,plain,
% 3.70/0.98      ( l1_orders_2(sK8) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6463,plain,
% 3.70/0.98      ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | r1_orders_2(sK8,X0,X1) != iProver_top
% 3.70/0.98      | r1_orders_2(sK6,X0,X1) = iProver_top ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_5078,c_34]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6464,plain,
% 3.70/0.98      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.70/0.98      | r1_orders_2(sK8,X0,X1) != iProver_top
% 3.70/0.98      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 3.70/0.98      inference(renaming,[status(thm)],[c_6463]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6475,plain,
% 3.70/0.98      ( sP0(X0,X1,sK8) = iProver_top
% 3.70/0.98      | r1_orders_2(sK6,X2,sK3(X0,X1,sK8)) = iProver_top
% 3.70/0.98      | r1_orders_2(sK8,X2,sK3(X0,X1,sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(X2,u1_struct_0(sK8)) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_2387,c_6464]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_9313,plain,
% 3.70/0.98      ( sP0(X0,X1,sK8) = iProver_top
% 3.70/0.98      | r1_orders_2(sK6,sK2(X0,X1,sK8),sK3(X0,X1,sK8)) = iProver_top
% 3.70/0.98      | m1_subset_1(sK2(X0,X1,sK8),u1_struct_0(sK8)) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_2388,c_6475]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_14,plain,
% 3.70/0.98      ( sP0(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) ),
% 3.70/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3649,plain,
% 3.70/0.98      ( sP0(X0,X1,sK8) | m1_subset_1(sK2(X0,X1,sK8),u1_struct_0(sK8)) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3665,plain,
% 3.70/0.98      ( sP0(X0,X1,sK8) = iProver_top
% 3.70/0.98      | m1_subset_1(sK2(X0,X1,sK8),u1_struct_0(sK8)) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_3649]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_9318,plain,
% 3.70/0.98      ( r1_orders_2(sK6,sK2(X0,X1,sK8),sK3(X0,X1,sK8)) = iProver_top
% 3.70/0.98      | sP0(X0,X1,sK8) = iProver_top ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_9313,c_3665]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_9319,plain,
% 3.70/0.98      ( sP0(X0,X1,sK8) = iProver_top
% 3.70/0.98      | r1_orders_2(sK6,sK2(X0,X1,sK8),sK3(X0,X1,sK8)) = iProver_top ),
% 3.70/0.98      inference(renaming,[status(thm)],[c_9318]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_9,plain,
% 3.70/0.98      ( sP0(X0,X1,X2) | k1_funct_1(X1,sK2(X0,X1,X2)) = sK4(X0,X1,X2) ),
% 3.70/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2391,plain,
% 3.70/0.98      ( k1_funct_1(X0,sK2(X1,X0,X2)) = sK4(X1,X0,X2)
% 3.70/0.98      | sP0(X1,X0,X2) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_5,plain,
% 3.70/0.98      ( ~ sP1(X0,X1,X2) | ~ sP0(X2,X1,X0) | v5_orders_3(X1,X0,X2) ),
% 3.70/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_17,negated_conjecture,
% 3.70/0.98      ( ~ v5_orders_3(sK11,sK8,sK9) ),
% 3.70/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_316,plain,
% 3.70/0.98      ( ~ sP1(X0,X1,X2)
% 3.70/0.98      | ~ sP0(X2,X1,X0)
% 3.70/0.98      | sK9 != X2
% 3.70/0.98      | sK8 != X0
% 3.70/0.98      | sK11 != X1 ),
% 3.70/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_17]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_317,plain,
% 3.70/0.98      ( ~ sP1(sK8,sK11,sK9) | ~ sP0(sK9,sK11,sK8) ),
% 3.70/0.98      inference(unflattening,[status(thm)],[c_316]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_16,plain,
% 3.70/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.70/0.98      | sP1(X1,X0,X2)
% 3.70/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.70/0.98      | ~ v1_funct_1(X0)
% 3.70/0.98      | ~ l1_orders_2(X1)
% 3.70/0.98      | ~ l1_orders_2(X2) ),
% 3.70/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_23,negated_conjecture,
% 3.70/0.98      ( v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) ),
% 3.70/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_353,plain,
% 3.70/0.98      ( sP1(X0,X1,X2)
% 3.70/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
% 3.70/0.98      | ~ v1_funct_1(X1)
% 3.70/0.98      | ~ l1_orders_2(X0)
% 3.70/0.98      | ~ l1_orders_2(X2)
% 3.70/0.98      | u1_struct_0(X2) != u1_struct_0(sK9)
% 3.70/0.98      | u1_struct_0(X0) != u1_struct_0(sK8)
% 3.70/0.98      | sK11 != X1 ),
% 3.70/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_354,plain,
% 3.70/0.98      ( sP1(X0,sK11,X1)
% 3.70/0.98      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.70/0.98      | ~ v1_funct_1(sK11)
% 3.70/0.98      | ~ l1_orders_2(X0)
% 3.70/0.98      | ~ l1_orders_2(X1)
% 3.70/0.98      | u1_struct_0(X1) != u1_struct_0(sK9)
% 3.70/0.98      | u1_struct_0(X0) != u1_struct_0(sK8) ),
% 3.70/0.98      inference(unflattening,[status(thm)],[c_353]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_24,negated_conjecture,
% 3.70/0.98      ( v1_funct_1(sK11) ),
% 3.70/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_358,plain,
% 3.70/0.98      ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.70/0.98      | sP1(X0,sK11,X1)
% 3.70/0.98      | ~ l1_orders_2(X0)
% 3.70/0.98      | ~ l1_orders_2(X1)
% 3.70/0.98      | u1_struct_0(X1) != u1_struct_0(sK9)
% 3.70/0.98      | u1_struct_0(X0) != u1_struct_0(sK8) ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_354,c_24]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_359,plain,
% 3.70/0.98      ( sP1(X0,sK11,X1)
% 3.70/0.98      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.70/0.98      | ~ l1_orders_2(X0)
% 3.70/0.98      | ~ l1_orders_2(X1)
% 3.70/0.98      | u1_struct_0(X1) != u1_struct_0(sK9)
% 3.70/0.98      | u1_struct_0(X0) != u1_struct_0(sK8) ),
% 3.70/0.98      inference(renaming,[status(thm)],[c_358]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_427,plain,
% 3.70/0.98      ( ~ sP0(sK9,sK11,sK8)
% 3.70/0.98      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.70/0.98      | ~ l1_orders_2(X0)
% 3.70/0.98      | ~ l1_orders_2(X1)
% 3.70/0.98      | u1_struct_0(X1) != u1_struct_0(sK9)
% 3.70/0.98      | u1_struct_0(X0) != u1_struct_0(sK8)
% 3.70/0.98      | sK9 != X1
% 3.70/0.98      | sK8 != X0
% 3.70/0.98      | sK11 != sK11 ),
% 3.70/0.98      inference(resolution_lifted,[status(thm)],[c_317,c_359]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_428,plain,
% 3.70/0.98      ( ~ sP0(sK9,sK11,sK8)
% 3.70/0.98      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
% 3.70/0.98      | ~ l1_orders_2(sK9)
% 3.70/0.98      | ~ l1_orders_2(sK8)
% 3.70/0.98      | u1_struct_0(sK9) != u1_struct_0(sK9)
% 3.70/0.98      | u1_struct_0(sK8) != u1_struct_0(sK8) ),
% 3.70/0.98      inference(unflattening,[status(thm)],[c_427]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_28,negated_conjecture,
% 3.70/0.98      ( l1_orders_2(sK9) ),
% 3.70/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_22,negated_conjecture,
% 3.70/0.98      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) ),
% 3.70/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_430,plain,
% 3.70/0.98      ( ~ sP0(sK9,sK11,sK8)
% 3.70/0.98      | u1_struct_0(sK9) != u1_struct_0(sK9)
% 3.70/0.98      | u1_struct_0(sK8) != u1_struct_0(sK8) ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_428,c_29,c_28,c_22]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1038,plain,
% 3.70/0.98      ( ~ sP0(sK9,sK11,sK8) ),
% 3.70/0.98      inference(equality_resolution_simp,[status(thm)],[c_430]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2377,plain,
% 3.70/0.98      ( sP0(sK9,sK11,sK8) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_1038]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3509,plain,
% 3.70/0.98      ( k1_funct_1(sK11,sK2(sK9,sK11,sK8)) = sK4(sK9,sK11,sK8) ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_2391,c_2377]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_8,plain,
% 3.70/0.98      ( sP0(X0,X1,X2) | k1_funct_1(X1,sK3(X0,X1,X2)) = sK5(X0,X1,X2) ),
% 3.70/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2392,plain,
% 3.70/0.98      ( k1_funct_1(X0,sK3(X1,X0,X2)) = sK5(X1,X0,X2)
% 3.70/0.98      | sP0(X1,X0,X2) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3531,plain,
% 3.70/0.98      ( k1_funct_1(sK11,sK3(sK9,sK11,sK8)) = sK5(sK9,sK11,sK8) ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_2392,c_2377]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6,plain,
% 3.70/0.98      ( ~ sP1(X0,X1,X2) | sP0(X2,X1,X0) | ~ v5_orders_3(X1,X0,X2) ),
% 3.70/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_18,negated_conjecture,
% 3.70/0.98      ( v5_orders_3(sK10,sK6,sK7) ),
% 3.70/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_326,plain,
% 3.70/0.98      ( ~ sP1(X0,X1,X2)
% 3.70/0.98      | sP0(X2,X1,X0)
% 3.70/0.98      | sK7 != X2
% 3.70/0.98      | sK6 != X0
% 3.70/0.98      | sK10 != X1 ),
% 3.70/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_327,plain,
% 3.70/0.98      ( ~ sP1(sK6,sK10,sK7) | sP0(sK7,sK10,sK6) ),
% 3.70/0.98      inference(unflattening,[status(thm)],[c_326]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_464,plain,
% 3.70/0.98      ( sP0(sK7,sK10,sK6)
% 3.70/0.98      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.70/0.98      | ~ l1_orders_2(X0)
% 3.70/0.98      | ~ l1_orders_2(X1)
% 3.70/0.98      | u1_struct_0(X1) != u1_struct_0(sK9)
% 3.70/0.98      | u1_struct_0(X0) != u1_struct_0(sK8)
% 3.70/0.98      | sK7 != X1
% 3.70/0.98      | sK6 != X0
% 3.70/0.98      | sK10 != sK11 ),
% 3.70/0.98      inference(resolution_lifted,[status(thm)],[c_327,c_359]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_465,plain,
% 3.70/0.98      ( sP0(sK7,sK10,sK6)
% 3.70/0.98      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 3.70/0.98      | ~ l1_orders_2(sK7)
% 3.70/0.98      | ~ l1_orders_2(sK6)
% 3.70/0.98      | u1_struct_0(sK7) != u1_struct_0(sK9)
% 3.70/0.98      | u1_struct_0(sK6) != u1_struct_0(sK8)
% 3.70/0.98      | sK10 != sK11 ),
% 3.70/0.98      inference(unflattening,[status(thm)],[c_464]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_30,negated_conjecture,
% 3.70/0.98      ( l1_orders_2(sK7) ),
% 3.70/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_19,negated_conjecture,
% 3.70/0.98      ( sK10 = sK11 ),
% 3.70/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_467,plain,
% 3.70/0.98      ( u1_struct_0(sK6) != u1_struct_0(sK8)
% 3.70/0.98      | u1_struct_0(sK7) != u1_struct_0(sK9)
% 3.70/0.98      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 3.70/0.98      | sP0(sK7,sK10,sK6) ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_465,c_31,c_30,c_19]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_468,plain,
% 3.70/0.98      ( sP0(sK7,sK10,sK6)
% 3.70/0.98      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 3.70/0.98      | u1_struct_0(sK7) != u1_struct_0(sK9)
% 3.70/0.98      | u1_struct_0(sK6) != u1_struct_0(sK8) ),
% 3.70/0.98      inference(renaming,[status(thm)],[c_467]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_26,negated_conjecture,
% 3.70/0.98      ( v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7)) ),
% 3.70/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_383,plain,
% 3.70/0.98      ( sP1(X0,X1,X2)
% 3.70/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
% 3.70/0.98      | ~ v1_funct_1(X1)
% 3.70/0.98      | ~ l1_orders_2(X0)
% 3.70/0.98      | ~ l1_orders_2(X2)
% 3.70/0.98      | u1_struct_0(X2) != u1_struct_0(sK7)
% 3.70/0.98      | u1_struct_0(X0) != u1_struct_0(sK6)
% 3.70/0.98      | sK10 != X1 ),
% 3.70/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_384,plain,
% 3.70/0.98      ( sP1(X0,sK10,X1)
% 3.70/0.98      | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.70/0.98      | ~ v1_funct_1(sK10)
% 3.70/0.98      | ~ l1_orders_2(X0)
% 3.70/0.98      | ~ l1_orders_2(X1)
% 3.70/0.98      | u1_struct_0(X1) != u1_struct_0(sK7)
% 3.70/0.98      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 3.70/0.98      inference(unflattening,[status(thm)],[c_383]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_27,negated_conjecture,
% 3.70/0.98      ( v1_funct_1(sK10) ),
% 3.70/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_388,plain,
% 3.70/0.98      ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.70/0.98      | sP1(X0,sK10,X1)
% 3.70/0.98      | ~ l1_orders_2(X0)
% 3.70/0.98      | ~ l1_orders_2(X1)
% 3.70/0.98      | u1_struct_0(X1) != u1_struct_0(sK7)
% 3.70/0.98      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_384,c_27]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_389,plain,
% 3.70/0.98      ( sP1(X0,sK10,X1)
% 3.70/0.98      | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.70/0.98      | ~ l1_orders_2(X0)
% 3.70/0.98      | ~ l1_orders_2(X1)
% 3.70/0.98      | u1_struct_0(X1) != u1_struct_0(sK7)
% 3.70/0.98      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 3.70/0.98      inference(renaming,[status(thm)],[c_388]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_484,plain,
% 3.70/0.98      ( sP0(sK7,sK10,sK6)
% 3.70/0.98      | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.70/0.98      | ~ l1_orders_2(X0)
% 3.70/0.98      | ~ l1_orders_2(X1)
% 3.70/0.98      | u1_struct_0(X1) != u1_struct_0(sK7)
% 3.70/0.98      | u1_struct_0(X0) != u1_struct_0(sK6)
% 3.70/0.98      | sK7 != X1
% 3.70/0.98      | sK6 != X0
% 3.70/0.98      | sK10 != sK10 ),
% 3.70/0.98      inference(resolution_lifted,[status(thm)],[c_327,c_389]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_485,plain,
% 3.70/0.98      ( sP0(sK7,sK10,sK6)
% 3.70/0.98      | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 3.70/0.98      | ~ l1_orders_2(sK7)
% 3.70/0.98      | ~ l1_orders_2(sK6)
% 3.70/0.98      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 3.70/0.98      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 3.70/0.98      inference(unflattening,[status(thm)],[c_484]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_25,negated_conjecture,
% 3.70/0.98      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
% 3.70/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_487,plain,
% 3.70/0.98      ( sP0(sK7,sK10,sK6)
% 3.70/0.98      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 3.70/0.98      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_485,c_31,c_30,c_25]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1030,plain,
% 3.70/0.98      ( sP0(sK7,sK10,sK6) ),
% 3.70/0.98      inference(equality_resolution_simp,[status(thm)],[c_487]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1033,plain,
% 3.70/0.98      ( sP0(sK7,sK10,sK6) ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_468,c_1030]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2378,plain,
% 3.70/0.98      ( sP0(sK7,sK10,sK6) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_1033]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2408,plain,
% 3.70/0.98      ( sP0(sK7,sK11,sK6) = iProver_top ),
% 3.70/0.98      inference(light_normalisation,[status(thm)],[c_2378,c_19]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_15,plain,
% 3.70/0.98      ( ~ sP0(X0,X1,X2)
% 3.70/0.98      | ~ r1_orders_2(X2,X3,X4)
% 3.70/0.98      | r1_orders_2(X0,k1_funct_1(X1,X3),k1_funct_1(X1,X4))
% 3.70/0.98      | ~ m1_subset_1(X4,u1_struct_0(X2))
% 3.70/0.98      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.70/0.98      | ~ m1_subset_1(k1_funct_1(X1,X4),u1_struct_0(X0))
% 3.70/0.98      | ~ m1_subset_1(k1_funct_1(X1,X3),u1_struct_0(X0)) ),
% 3.70/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2385,plain,
% 3.70/0.98      ( sP0(X0,X1,X2) != iProver_top
% 3.70/0.98      | r1_orders_2(X2,X3,X4) != iProver_top
% 3.70/0.98      | r1_orders_2(X0,k1_funct_1(X1,X3),k1_funct_1(X1,X4)) = iProver_top
% 3.70/0.98      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 3.70/0.98      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 3.70/0.98      | m1_subset_1(k1_funct_1(X1,X4),u1_struct_0(X0)) != iProver_top
% 3.70/0.98      | m1_subset_1(k1_funct_1(X1,X3),u1_struct_0(X0)) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3373,plain,
% 3.70/0.98      ( r1_orders_2(sK7,k1_funct_1(sK11,X0),k1_funct_1(sK11,X1)) = iProver_top
% 3.70/0.98      | r1_orders_2(sK6,X0,X1) != iProver_top
% 3.70/0.98      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.70/0.98      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.70/0.98      | m1_subset_1(k1_funct_1(sK11,X1),u1_struct_0(sK7)) != iProver_top
% 3.70/0.98      | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK7)) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_2408,c_2385]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_20,negated_conjecture,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
% 3.70/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3126,plain,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(X0,X1)
% 3.70/0.98      | u1_struct_0(sK7) = X0
% 3.70/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_20,c_2395]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3173,plain,
% 3.70/0.98      ( u1_struct_0(sK9) = u1_struct_0(sK7)
% 3.70/0.98      | m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)))) != iProver_top ),
% 3.70/0.98      inference(equality_resolution,[status(thm)],[c_3126]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3185,plain,
% 3.70/0.98      ( ~ m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
% 3.70/0.98      | u1_struct_0(sK9) = u1_struct_0(sK7) ),
% 3.70/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3173]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3833,plain,
% 3.70/0.98      ( m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
% 3.70/0.98      | ~ l1_orders_2(sK9) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3869,plain,
% 3.70/0.98      ( u1_struct_0(sK9) = u1_struct_0(sK7) ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_3173,c_28,c_3185,c_3833]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_4531,plain,
% 3.70/0.98      ( r1_orders_2(sK7,k1_funct_1(sK11,X0),k1_funct_1(sK11,X1)) = iProver_top
% 3.70/0.98      | r1_orders_2(sK6,X0,X1) != iProver_top
% 3.70/0.98      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(k1_funct_1(sK11,X1),u1_struct_0(sK9)) != iProver_top
% 3.70/0.98      | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK9)) != iProver_top ),
% 3.70/0.98      inference(light_normalisation,[status(thm)],[c_3373,c_3300,c_3869]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_4544,plain,
% 3.70/0.98      ( r1_orders_2(sK7,k1_funct_1(sK11,X0),sK5(sK9,sK11,sK8)) = iProver_top
% 3.70/0.98      | r1_orders_2(sK6,X0,sK3(sK9,sK11,sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(sK3(sK9,sK11,sK8),u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK9)) != iProver_top
% 3.70/0.98      | m1_subset_1(k1_funct_1(sK11,sK3(sK9,sK11,sK8)),u1_struct_0(sK9)) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_3531,c_4531]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_4551,plain,
% 3.70/0.98      ( r1_orders_2(sK7,k1_funct_1(sK11,X0),sK5(sK9,sK11,sK8)) = iProver_top
% 3.70/0.98      | r1_orders_2(sK6,X0,sK3(sK9,sK11,sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(sK3(sK9,sK11,sK8),u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top
% 3.70/0.98      | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK9)) != iProver_top ),
% 3.70/0.98      inference(light_normalisation,[status(thm)],[c_4544,c_3531]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_766,plain,
% 3.70/0.98      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2))
% 3.70/0.98      | u1_struct_0(sK9) != u1_struct_0(sK9)
% 3.70/0.98      | u1_struct_0(sK8) != u1_struct_0(sK8)
% 3.70/0.98      | sK9 != X0
% 3.70/0.98      | sK8 != X2
% 3.70/0.98      | sK11 != X1 ),
% 3.70/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_430]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_767,plain,
% 3.70/0.98      ( m1_subset_1(sK3(sK9,sK11,sK8),u1_struct_0(sK8)) ),
% 3.70/0.98      inference(unflattening,[status(thm)],[c_766]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_768,plain,
% 3.70/0.98      ( m1_subset_1(sK3(sK9,sK11,sK8),u1_struct_0(sK8)) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_767]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_10,plain,
% 3.70/0.98      ( sP0(X0,X1,X2) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ),
% 3.70/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_835,plain,
% 3.70/0.98      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
% 3.70/0.98      | u1_struct_0(sK9) != u1_struct_0(sK9)
% 3.70/0.98      | u1_struct_0(sK8) != u1_struct_0(sK8)
% 3.70/0.98      | sK9 != X0
% 3.70/0.98      | sK8 != X2
% 3.70/0.98      | sK11 != X1 ),
% 3.70/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_430]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_836,plain,
% 3.70/0.98      ( m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) ),
% 3.70/0.98      inference(unflattening,[status(thm)],[c_835]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_837,plain,
% 3.70/0.98      ( m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_836]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_7689,plain,
% 3.70/0.98      ( r1_orders_2(sK7,k1_funct_1(sK11,X0),sK5(sK9,sK11,sK8)) = iProver_top
% 3.70/0.98      | r1_orders_2(sK6,X0,sK3(sK9,sK11,sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK9)) != iProver_top ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_4551,c_768,c_837]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_7699,plain,
% 3.70/0.98      ( r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
% 3.70/0.98      | r1_orders_2(sK6,sK2(sK9,sK11,sK8),sK3(sK9,sK11,sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(sK2(sK9,sK11,sK8),u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(k1_funct_1(sK11,sK2(sK9,sK11,sK8)),u1_struct_0(sK9)) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_3509,c_7689]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_7752,plain,
% 3.70/0.98      ( r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
% 3.70/0.98      | r1_orders_2(sK6,sK2(sK9,sK11,sK8),sK3(sK9,sK11,sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(sK2(sK9,sK11,sK8),u1_struct_0(sK8)) != iProver_top
% 3.70/0.98      | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top ),
% 3.70/0.98      inference(light_normalisation,[status(thm)],[c_7699,c_3509]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_33,plain,
% 3.70/0.98      ( l1_orders_2(sK7) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_35,plain,
% 3.70/0.98      ( l1_orders_2(sK9) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_743,plain,
% 3.70/0.98      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2))
% 3.70/0.98      | u1_struct_0(sK9) != u1_struct_0(sK9)
% 3.70/0.98      | u1_struct_0(sK8) != u1_struct_0(sK8)
% 3.70/0.98      | sK9 != X0
% 3.70/0.98      | sK8 != X2
% 3.70/0.98      | sK11 != X1 ),
% 3.70/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_430]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_744,plain,
% 3.70/0.98      ( m1_subset_1(sK2(sK9,sK11,sK8),u1_struct_0(sK8)) ),
% 3.70/0.98      inference(unflattening,[status(thm)],[c_743]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_745,plain,
% 3.70/0.98      ( m1_subset_1(sK2(sK9,sK11,sK8),u1_struct_0(sK8)) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_11,plain,
% 3.70/0.98      ( sP0(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ),
% 3.70/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_812,plain,
% 3.70/0.98      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
% 3.70/0.98      | u1_struct_0(sK9) != u1_struct_0(sK9)
% 3.70/0.98      | u1_struct_0(sK8) != u1_struct_0(sK8)
% 3.70/0.98      | sK9 != X0
% 3.70/0.98      | sK8 != X2
% 3.70/0.98      | sK11 != X1 ),
% 3.70/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_430]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_813,plain,
% 3.70/0.98      ( m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) ),
% 3.70/0.98      inference(unflattening,[status(thm)],[c_812]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_814,plain,
% 3.70/0.98      ( m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) = iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_813]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_7,plain,
% 3.70/0.98      ( sP0(X0,X1,X2) | ~ r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2)) ),
% 3.70/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_900,plain,
% 3.70/0.98      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2))
% 3.70/0.98      | u1_struct_0(sK9) != u1_struct_0(sK9)
% 3.70/0.98      | u1_struct_0(sK8) != u1_struct_0(sK8)
% 3.70/0.98      | sK9 != X0
% 3.70/0.98      | sK8 != X2
% 3.70/0.98      | sK11 != X1 ),
% 3.70/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_430]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_901,plain,
% 3.70/0.98      ( ~ r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) ),
% 3.70/0.98      inference(unflattening,[status(thm)],[c_900]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_902,plain,
% 3.70/0.98      ( r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_901]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3875,plain,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
% 3.70/0.98      inference(demodulation,[status(thm)],[c_3869,c_20]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1,plain,
% 3.70/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.70/0.98      | X2 = X0
% 3.70/0.98      | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
% 3.70/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2396,plain,
% 3.70/0.98      ( X0 = X1
% 3.70/0.98      | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
% 3.70/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_4191,plain,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(X0,X1)
% 3.70/0.98      | u1_orders_2(sK7) = X1
% 3.70/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_3875,c_2396]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2397,plain,
% 3.70/0.98      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
% 3.70/0.98      | l1_orders_2(X0) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3892,plain,
% 3.70/0.98      ( m1_subset_1(u1_orders_2(sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)))) = iProver_top
% 3.70/0.98      | l1_orders_2(sK7) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_3869,c_2397]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_4193,plain,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(X0,X1)
% 3.70/0.98      | u1_orders_2(sK7) = X1
% 3.70/0.98      | m1_subset_1(u1_orders_2(sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)))) != iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_3875,c_2396]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_4432,plain,
% 3.70/0.98      ( u1_orders_2(sK7) = X1
% 3.70/0.98      | g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(X0,X1) ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_4191,c_33,c_3892,c_4193]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_4433,plain,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(X0,X1)
% 3.70/0.98      | u1_orders_2(sK7) = X1 ),
% 3.70/0.98      inference(renaming,[status(thm)],[c_4432]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_4438,plain,
% 3.70/0.98      ( u1_orders_2(sK9) = u1_orders_2(sK7) ),
% 3.70/0.98      inference(equality_resolution,[status(thm)],[c_4433]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_5255,plain,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
% 3.70/0.98      inference(demodulation,[status(thm)],[c_4438,c_3875]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2915,plain,
% 3.70/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
% 3.70/0.98      | X1 = u1_struct_0(sK9)
% 3.70/0.98      | g1_orders_2(X1,X2) != g1_orders_2(u1_struct_0(sK9),X0) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_3832,plain,
% 3.70/0.98      ( ~ m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
% 3.70/0.98      | X0 = u1_struct_0(sK9)
% 3.70/0.98      | g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_2915]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_5621,plain,
% 3.70/0.98      ( ~ m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
% 3.70/0.98      | g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) != g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9))
% 3.70/0.98      | u1_struct_0(sK7) = u1_struct_0(sK9) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_3832]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1995,plain,
% 3.70/0.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.70/0.98      theory(equality) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2685,plain,
% 3.70/0.98      ( m1_subset_1(X0,X1)
% 3.70/0.98      | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9))
% 3.70/0.98      | X0 != sK5(sK9,sK11,sK8)
% 3.70/0.98      | X1 != u1_struct_0(sK9) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_1995]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2933,plain,
% 3.70/0.98      ( m1_subset_1(X0,u1_struct_0(X1))
% 3.70/0.98      | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9))
% 3.70/0.98      | X0 != sK5(sK9,sK11,sK8)
% 3.70/0.98      | u1_struct_0(X1) != u1_struct_0(sK9) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_2685]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6023,plain,
% 3.70/0.98      ( m1_subset_1(X0,u1_struct_0(sK7))
% 3.70/0.98      | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9))
% 3.70/0.98      | X0 != sK5(sK9,sK11,sK8)
% 3.70/0.98      | u1_struct_0(sK7) != u1_struct_0(sK9) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_2933]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_8491,plain,
% 3.70/0.98      ( m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK7))
% 3.70/0.98      | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9))
% 3.70/0.98      | sK5(sK9,sK11,sK8) != sK5(sK9,sK11,sK8)
% 3.70/0.98      | u1_struct_0(sK7) != u1_struct_0(sK9) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_6023]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_8493,plain,
% 3.70/0.98      ( sK5(sK9,sK11,sK8) != sK5(sK9,sK11,sK8)
% 3.70/0.98      | u1_struct_0(sK7) != u1_struct_0(sK9)
% 3.70/0.98      | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK7)) = iProver_top
% 3.70/0.98      | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_8491]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1989,plain,( X0 = X0 ),theory(equality) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_8492,plain,
% 3.70/0.98      ( sK5(sK9,sK11,sK8) = sK5(sK9,sK11,sK8) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_1989]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2700,plain,
% 3.70/0.98      ( m1_subset_1(X0,X1)
% 3.70/0.98      | ~ m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9))
% 3.70/0.98      | X0 != sK4(sK9,sK11,sK8)
% 3.70/0.98      | X1 != u1_struct_0(sK9) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_1995]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_6028,plain,
% 3.70/0.98      ( m1_subset_1(X0,u1_struct_0(sK7))
% 3.70/0.98      | ~ m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9))
% 3.70/0.98      | X0 != sK4(sK9,sK11,sK8)
% 3.70/0.98      | u1_struct_0(sK7) != u1_struct_0(sK9) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_2700]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_8501,plain,
% 3.70/0.98      ( m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK7))
% 3.70/0.98      | ~ m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9))
% 3.70/0.98      | sK4(sK9,sK11,sK8) != sK4(sK9,sK11,sK8)
% 3.70/0.98      | u1_struct_0(sK7) != u1_struct_0(sK9) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_6028]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_8503,plain,
% 3.70/0.98      ( sK4(sK9,sK11,sK8) != sK4(sK9,sK11,sK8)
% 3.70/0.98      | u1_struct_0(sK7) != u1_struct_0(sK9)
% 3.70/0.98      | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK7)) = iProver_top
% 3.70/0.98      | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_8501]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_8502,plain,
% 3.70/0.98      ( sK4(sK9,sK11,sK8) = sK4(sK9,sK11,sK8) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_1989]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1990,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_4705,plain,
% 3.70/0.98      ( g1_orders_2(X0,X1) != X2
% 3.70/0.98      | g1_orders_2(X0,X1) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
% 3.70/0.98      | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != X2 ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_1990]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_7638,plain,
% 3.70/0.98      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
% 3.70/0.98      | g1_orders_2(X0,X1) = g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
% 3.70/0.98      | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(X2,X3) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_4705]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_13464,plain,
% 3.70/0.98      ( g1_orders_2(X0,X1) = g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7))
% 3.70/0.98      | g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9))
% 3.70/0.98      | g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) != g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_7638]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_13960,plain,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) != g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9))
% 3.70/0.98      | g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) = g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7))
% 3.70/0.98      | g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_13464]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2675,plain,
% 3.70/0.98      ( ~ r1_orders_2(X0,X1,sK5(sK9,sK11,sK8))
% 3.70/0.98      | r1_orders_2(sK9,X1,sK5(sK9,sK11,sK8))
% 3.70/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.70/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 3.70/0.98      | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(X0))
% 3.70/0.98      | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9))
% 3.70/0.98      | ~ l1_orders_2(X0)
% 3.70/0.98      | ~ l1_orders_2(sK9)
% 3.70/0.98      | g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_2977,plain,
% 3.70/0.98      ( ~ r1_orders_2(X0,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8))
% 3.70/0.98      | r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8))
% 3.70/0.98      | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(X0))
% 3.70/0.98      | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9))
% 3.70/0.98      | ~ m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(X0))
% 3.70/0.98      | ~ m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9))
% 3.70/0.98      | ~ l1_orders_2(X0)
% 3.70/0.98      | ~ l1_orders_2(sK9)
% 3.70/0.98      | g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_2675]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_14980,plain,
% 3.70/0.98      ( ~ r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8))
% 3.70/0.98      | r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8))
% 3.70/0.98      | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK7))
% 3.70/0.98      | ~ m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9))
% 3.70/0.98      | ~ m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK7))
% 3.70/0.98      | ~ m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9))
% 3.70/0.98      | ~ l1_orders_2(sK7)
% 3.70/0.98      | ~ l1_orders_2(sK9)
% 3.70/0.98      | g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) ),
% 3.70/0.98      inference(instantiation,[status(thm)],[c_2977]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_14984,plain,
% 3.70/0.98      ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7))
% 3.70/0.98      | r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) != iProver_top
% 3.70/0.98      | r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
% 3.70/0.98      | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK7)) != iProver_top
% 3.70/0.98      | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top
% 3.70/0.98      | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK7)) != iProver_top
% 3.70/0.98      | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top
% 3.70/0.98      | l1_orders_2(sK7) != iProver_top
% 3.70/0.98      | l1_orders_2(sK9) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_14980]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_15665,plain,
% 3.70/0.98      ( r1_orders_2(sK6,sK2(sK9,sK11,sK8),sK3(sK9,sK11,sK8)) != iProver_top ),
% 3.70/0.98      inference(global_propositional_subsumption,
% 3.70/0.98                [status(thm)],
% 3.70/0.98                [c_7752,c_33,c_28,c_35,c_20,c_745,c_814,c_837,c_902,
% 3.70/0.98                 c_3833,c_5255,c_5621,c_8493,c_8492,c_8503,c_8502,
% 3.70/0.98                 c_13960,c_14984]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_15670,plain,
% 3.70/0.98      ( sP0(sK9,sK11,sK8) = iProver_top ),
% 3.70/0.98      inference(superposition,[status(thm)],[c_9319,c_15665]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(c_1039,plain,
% 3.70/0.98      ( sP0(sK9,sK11,sK8) != iProver_top ),
% 3.70/0.98      inference(predicate_to_equality,[status(thm)],[c_1038]) ).
% 3.70/0.98  
% 3.70/0.98  cnf(contradiction,plain,
% 3.70/0.98      ( $false ),
% 3.70/0.98      inference(minisat,[status(thm)],[c_15670,c_1039]) ).
% 3.70/0.98  
% 3.70/0.98  
% 3.70/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/0.98  
% 3.70/0.98  ------                               Statistics
% 3.70/0.98  
% 3.70/0.98  ------ General
% 3.70/0.98  
% 3.70/0.98  abstr_ref_over_cycles:                  0
% 3.70/0.98  abstr_ref_under_cycles:                 0
% 3.70/0.98  gc_basic_clause_elim:                   0
% 3.70/0.98  forced_gc_time:                         0
% 3.70/0.98  parsing_time:                           0.01
% 3.70/0.98  unif_index_cands_time:                  0.
% 3.70/0.98  unif_index_add_time:                    0.
% 3.70/0.98  orderings_time:                         0.
% 3.70/0.98  out_proof_time:                         0.014
% 3.70/0.98  total_time:                             0.477
% 3.70/0.98  num_of_symbols:                         56
% 3.70/0.98  num_of_terms:                           16129
% 3.70/0.98  
% 3.70/0.98  ------ Preprocessing
% 3.70/0.98  
% 3.70/0.98  num_of_splits:                          0
% 3.70/0.98  num_of_split_atoms:                     0
% 3.70/0.98  num_of_reused_defs:                     0
% 3.70/0.98  num_eq_ax_congr_red:                    65
% 3.70/0.98  num_of_sem_filtered_clauses:            2
% 3.70/0.98  num_of_subtypes:                        0
% 3.70/0.98  monotx_restored_types:                  0
% 3.70/0.98  sat_num_of_epr_types:                   0
% 3.70/0.98  sat_num_of_non_cyclic_types:            0
% 3.70/0.98  sat_guarded_non_collapsed_types:        0
% 3.70/0.98  num_pure_diseq_elim:                    0
% 3.70/0.98  simp_replaced_by:                       0
% 3.70/0.98  res_preprocessed:                       157
% 3.70/0.98  prep_upred:                             0
% 3.70/0.98  prep_unflattend:                        124
% 3.70/0.98  smt_new_axioms:                         0
% 3.70/0.98  pred_elim_cands:                        4
% 3.70/0.98  pred_elim:                              4
% 3.70/0.98  pred_elim_cl:                           4
% 3.70/0.98  pred_elim_cycles:                       7
% 3.70/0.98  merged_defs:                            0
% 3.70/0.98  merged_defs_ncl:                        0
% 3.70/0.98  bin_hyper_res:                          0
% 3.70/0.98  prep_cycles:                            5
% 3.70/0.98  pred_elim_time:                         0.025
% 3.70/0.98  splitting_time:                         0.
% 3.70/0.98  sem_filter_time:                        0.
% 3.70/0.99  monotx_time:                            0.001
% 3.70/0.99  subtype_inf_time:                       0.
% 3.70/0.99  
% 3.70/0.99  ------ Problem properties
% 3.70/0.99  
% 3.70/0.99  clauses:                                25
% 3.70/0.99  conjectures:                            9
% 3.70/0.99  epr:                                    8
% 3.70/0.99  horn:                                   18
% 3.70/0.99  ground:                                 12
% 3.70/0.99  unary:                                  11
% 3.70/0.99  binary:                                 10
% 3.70/0.99  lits:                                   53
% 3.70/0.99  lits_eq:                                12
% 3.70/0.99  fd_pure:                                0
% 3.70/0.99  fd_pseudo:                              0
% 3.70/0.99  fd_cond:                                0
% 3.70/0.99  fd_pseudo_cond:                         2
% 3.70/0.99  ac_symbols:                             0
% 3.70/0.99  
% 3.70/0.99  ------ Propositional Solver
% 3.70/0.99  
% 3.70/0.99  prop_solver_calls:                      36
% 3.70/0.99  prop_fast_solver_calls:                 1897
% 3.70/0.99  smt_solver_calls:                       0
% 3.70/0.99  smt_fast_solver_calls:                  0
% 3.70/0.99  prop_num_of_clauses:                    4481
% 3.70/0.99  prop_preprocess_simplified:             9591
% 3.70/0.99  prop_fo_subsumed:                       62
% 3.70/0.99  prop_solver_time:                       0.
% 3.70/0.99  smt_solver_time:                        0.
% 3.70/0.99  smt_fast_solver_time:                   0.
% 3.70/0.99  prop_fast_solver_time:                  0.
% 3.70/0.99  prop_unsat_core_time:                   0.
% 3.70/0.99  
% 3.70/0.99  ------ QBF
% 3.70/0.99  
% 3.70/0.99  qbf_q_res:                              0
% 3.70/0.99  qbf_num_tautologies:                    0
% 3.70/0.99  qbf_prep_cycles:                        0
% 3.70/0.99  
% 3.70/0.99  ------ BMC1
% 3.70/0.99  
% 3.70/0.99  bmc1_current_bound:                     -1
% 3.70/0.99  bmc1_last_solved_bound:                 -1
% 3.70/0.99  bmc1_unsat_core_size:                   -1
% 3.70/0.99  bmc1_unsat_core_parents_size:           -1
% 3.70/0.99  bmc1_merge_next_fun:                    0
% 3.70/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.70/0.99  
% 3.70/0.99  ------ Instantiation
% 3.70/0.99  
% 3.70/0.99  inst_num_of_clauses:                    1307
% 3.70/0.99  inst_num_in_passive:                    590
% 3.70/0.99  inst_num_in_active:                     704
% 3.70/0.99  inst_num_in_unprocessed:                13
% 3.70/0.99  inst_num_of_loops:                      720
% 3.70/0.99  inst_num_of_learning_restarts:          0
% 3.70/0.99  inst_num_moves_active_passive:          11
% 3.70/0.99  inst_lit_activity:                      0
% 3.70/0.99  inst_lit_activity_moves:                0
% 3.70/0.99  inst_num_tautologies:                   0
% 3.70/0.99  inst_num_prop_implied:                  0
% 3.70/0.99  inst_num_existing_simplified:           0
% 3.70/0.99  inst_num_eq_res_simplified:             0
% 3.70/0.99  inst_num_child_elim:                    0
% 3.70/0.99  inst_num_of_dismatching_blockings:      1421
% 3.70/0.99  inst_num_of_non_proper_insts:           1900
% 3.70/0.99  inst_num_of_duplicates:                 0
% 3.70/0.99  inst_inst_num_from_inst_to_res:         0
% 3.70/0.99  inst_dismatching_checking_time:         0.
% 3.70/0.99  
% 3.70/0.99  ------ Resolution
% 3.70/0.99  
% 3.70/0.99  res_num_of_clauses:                     0
% 3.70/0.99  res_num_in_passive:                     0
% 3.70/0.99  res_num_in_active:                      0
% 3.70/0.99  res_num_of_loops:                       162
% 3.70/0.99  res_forward_subset_subsumed:            206
% 3.70/0.99  res_backward_subset_subsumed:           6
% 3.70/0.99  res_forward_subsumed:                   0
% 3.70/0.99  res_backward_subsumed:                  2
% 3.70/0.99  res_forward_subsumption_resolution:     0
% 3.70/0.99  res_backward_subsumption_resolution:    0
% 3.70/0.99  res_clause_to_clause_subsumption:       1421
% 3.70/0.99  res_orphan_elimination:                 0
% 3.70/0.99  res_tautology_del:                      170
% 3.70/0.99  res_num_eq_res_simplified:              2
% 3.70/0.99  res_num_sel_changes:                    0
% 3.70/0.99  res_moves_from_active_to_pass:          0
% 3.70/0.99  
% 3.70/0.99  ------ Superposition
% 3.70/0.99  
% 3.70/0.99  sup_time_total:                         0.
% 3.70/0.99  sup_time_generating:                    0.
% 3.70/0.99  sup_time_sim_full:                      0.
% 3.70/0.99  sup_time_sim_immed:                     0.
% 3.70/0.99  
% 3.70/0.99  sup_num_of_clauses:                     281
% 3.70/0.99  sup_num_in_active:                      131
% 3.70/0.99  sup_num_in_passive:                     150
% 3.70/0.99  sup_num_of_loops:                       143
% 3.70/0.99  sup_fw_superposition:                   159
% 3.70/0.99  sup_bw_superposition:                   161
% 3.70/0.99  sup_immediate_simplified:               144
% 3.70/0.99  sup_given_eliminated:                   3
% 3.70/0.99  comparisons_done:                       0
% 3.70/0.99  comparisons_avoided:                    15
% 3.70/0.99  
% 3.70/0.99  ------ Simplifications
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  sim_fw_subset_subsumed:                 4
% 3.70/0.99  sim_bw_subset_subsumed:                 9
% 3.70/0.99  sim_fw_subsumed:                        12
% 3.70/0.99  sim_bw_subsumed:                        0
% 3.70/0.99  sim_fw_subsumption_res:                 17
% 3.70/0.99  sim_bw_subsumption_res:                 0
% 3.70/0.99  sim_tautology_del:                      9
% 3.70/0.99  sim_eq_tautology_del:                   13
% 3.70/0.99  sim_eq_res_simp:                        0
% 3.70/0.99  sim_fw_demodulated:                     2
% 3.70/0.99  sim_bw_demodulated:                     13
% 3.70/0.99  sim_light_normalised:                   138
% 3.70/0.99  sim_joinable_taut:                      0
% 3.70/0.99  sim_joinable_simp:                      0
% 3.70/0.99  sim_ac_normalised:                      0
% 3.70/0.99  sim_smt_subsumption:                    0
% 3.70/0.99  
%------------------------------------------------------------------------------
