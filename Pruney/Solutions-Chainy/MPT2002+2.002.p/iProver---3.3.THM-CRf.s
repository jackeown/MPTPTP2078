%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:37 EST 2020

% Result     : Theorem 7.03s
% Output     : CNFRefutation 7.03s
% Verified   : 
% Statistics : Number of formulae       :  222 (2236 expanded)
%              Number of clauses        :  150 ( 484 expanded)
%              Number of leaves         :   18 ( 895 expanded)
%              Depth                    :   31
%              Number of atoms          : 1098 (29958 expanded)
%              Number of equality atoms :  507 (7236 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,plain,(
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

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f28,plain,(
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

fof(f27,plain,(
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

fof(f26,plain,(
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

fof(f25,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f28,f27,f26,f25])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | k1_funct_1(X1,sK3(X0,X1,X2)) = sK5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f19,plain,(
    ! [X0,X2,X1] :
      ( ( v5_orders_3(X2,X0,X1)
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X0,X2,X1] :
      ( ( ( v5_orders_3(X2,X0,X1)
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ v5_orders_3(X2,X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_orders_3(X1,X0,X2)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v5_orders_3(X1,X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f21])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v5_orders_3(X1,X0,X2)
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
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
    inference(pure_predicate_removal,[],[f7])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,
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

fof(f36,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f17,f35,f34,f33,f32,f31,f30])).

fof(f68,plain,(
    ~ v5_orders_3(sK11,sK8,sK9) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f13,f19,f18])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,(
    g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X0,X2,X3)
                              & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r1_orders_2(X0,X2,X3)
                          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r1_orders_2(X0,X2,X3)
                          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X3)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f72,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X4,X5)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r1_orders_2(X0,X9,k1_funct_1(X1,X8))
      | k1_funct_1(X1,X7) != X9
      | ~ m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0))
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | ~ r1_orders_2(X2,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f43])).

fof(f70,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r1_orders_2(X0,k1_funct_1(X1,X7),k1_funct_1(X1,X8))
      | ~ m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0))
      | ~ m1_subset_1(k1_funct_1(X1,X7),u1_struct_0(X0))
      | ~ r1_orders_2(X2,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f69])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | k1_funct_1(X1,sK2(X0,X1,X2)) = sK4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | ~ v5_orders_3(X1,X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    v5_orders_3(sK10,sK6,sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    sK10 = sK11 ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_7,plain,
    ( sP0(X0,X1,X2)
    | k1_funct_1(X1,sK3(X0,X1,X2)) = sK5(X0,X1,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2456,plain,
    ( k1_funct_1(X0,sK3(X1,X0,X2)) = sK5(X1,X0,X2)
    | sP0(X1,X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | v5_orders_3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,negated_conjecture,
    ( ~ v5_orders_3(sK11,sK8,sK9) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_321,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | sK9 != X2
    | sK8 != X0
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_322,plain,
    ( ~ sP1(sK8,sK11,sK9)
    | ~ sP0(sK9,sK11,sK8) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | sP1(X1,X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_358,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
    | ~ v1_funct_1(X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X2)
    | u1_struct_0(X2) != u1_struct_0(sK9)
    | u1_struct_0(X0) != u1_struct_0(sK8)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_359,plain,
    ( sP1(X0,sK11,X1)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK11)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK9)
    | u1_struct_0(X0) != u1_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_363,plain,
    ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | sP1(X0,sK11,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK9)
    | u1_struct_0(X0) != u1_struct_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_24])).

cnf(c_364,plain,
    ( sP1(X0,sK11,X1)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK9)
    | u1_struct_0(X0) != u1_struct_0(sK8) ),
    inference(renaming,[status(thm)],[c_363])).

cnf(c_432,plain,
    ( ~ sP0(sK9,sK11,sK8)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK9)
    | u1_struct_0(X0) != u1_struct_0(sK8)
    | sK9 != X1
    | sK8 != X0
    | sK11 != sK11 ),
    inference(resolution_lifted,[status(thm)],[c_322,c_364])).

cnf(c_433,plain,
    ( ~ sP0(sK9,sK11,sK8)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
    | ~ l1_orders_2(sK9)
    | ~ l1_orders_2(sK8)
    | u1_struct_0(sK9) != u1_struct_0(sK9)
    | u1_struct_0(sK8) != u1_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_29,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_28,negated_conjecture,
    ( l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_435,plain,
    ( ~ sP0(sK9,sK11,sK8)
    | u1_struct_0(sK9) != u1_struct_0(sK9)
    | u1_struct_0(sK8) != u1_struct_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_433,c_29,c_28,c_22])).

cnf(c_1052,plain,
    ( ~ sP0(sK9,sK11,sK8) ),
    inference(equality_resolution_simp,[status(thm)],[c_435])).

cnf(c_2440,plain,
    ( sP0(sK9,sK11,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1052])).

cnf(c_4462,plain,
    ( k1_funct_1(sK11,sK3(sK9,sK11,sK8)) = sK5(sK9,sK11,sK8) ),
    inference(superposition,[status(thm)],[c_2456,c_2440])).

cnf(c_11,plain,
    ( r1_orders_2(X0,sK2(X1,X2,X0),sK3(X1,X2,X0))
    | sP0(X1,X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2452,plain,
    ( r1_orders_2(X0,sK2(X1,X2,X0),sK3(X1,X2,X0)) = iProver_top
    | sP0(X1,X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2451,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2444,plain,
    ( l1_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2458,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0))
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2937,plain,
    ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) = k7_lattice3(k7_lattice3(sK8)) ),
    inference(superposition,[status(thm)],[c_2444,c_2458])).

cnf(c_21,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3117,plain,
    ( g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = k7_lattice3(k7_lattice3(sK8)) ),
    inference(demodulation,[status(thm)],[c_2937,c_21])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2459,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4756,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK8))
    | u1_struct_0(sK6) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3117,c_2459])).

cnf(c_31,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_32,plain,
    ( l1_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_0,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_88,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_90,plain,
    ( m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) = iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(c_4760,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK8))
    | u1_struct_0(sK6) = X0
    | m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3117,c_2459])).

cnf(c_4893,plain,
    ( u1_struct_0(sK6) = X0
    | g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4756,c_32,c_90,c_4760])).

cnf(c_4894,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK8))
    | u1_struct_0(sK6) = X0 ),
    inference(renaming,[status(thm)],[c_4893])).

cnf(c_4901,plain,
    ( u1_struct_0(sK8) = u1_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_2937,c_4894])).

cnf(c_16,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X3)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2448,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | r1_orders_2(X1,X2,X3) != iProver_top
    | r1_orders_2(X0,X2,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3374,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK8))
    | r1_orders_2(X0,X1,X2) != iProver_top
    | r1_orders_2(sK6,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3117,c_2448])).

cnf(c_3836,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r1_orders_2(sK6,X1,X2) = iProver_top
    | r1_orders_2(X0,X1,X2) != iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3374,c_32])).

cnf(c_3837,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK8))
    | r1_orders_2(X0,X1,X2) != iProver_top
    | r1_orders_2(sK6,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3836])).

cnf(c_3851,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2937,c_3837])).

cnf(c_34,plain,
    ( l1_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4314,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r1_orders_2(sK8,X0,X1) != iProver_top
    | r1_orders_2(sK6,X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3851,c_34])).

cnf(c_4315,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4314])).

cnf(c_5013,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4901,c_4315])).

cnf(c_9070,plain,
    ( r1_orders_2(sK6,X0,sK3(X1,X2,sK8)) = iProver_top
    | r1_orders_2(sK8,X0,sK3(X1,X2,sK8)) != iProver_top
    | sP0(X1,X2,sK8) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2451,c_5013])).

cnf(c_9536,plain,
    ( r1_orders_2(sK6,sK2(X0,X1,sK8),sK3(X0,X1,sK8)) = iProver_top
    | sP0(X0,X1,sK8) = iProver_top
    | m1_subset_1(sK2(X0,X1,sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2452,c_9070])).

cnf(c_13,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3924,plain,
    ( sP0(X0,X1,sK8)
    | m1_subset_1(sK2(X0,X1,sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3940,plain,
    ( sP0(X0,X1,sK8) = iProver_top
    | m1_subset_1(sK2(X0,X1,sK8),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3924])).

cnf(c_9541,plain,
    ( sP0(X0,X1,sK8) = iProver_top
    | r1_orders_2(sK6,sK2(X0,X1,sK8),sK3(X0,X1,sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9536,c_3940])).

cnf(c_9542,plain,
    ( r1_orders_2(sK6,sK2(X0,X1,sK8),sK3(X0,X1,sK8)) = iProver_top
    | sP0(X0,X1,sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_9541])).

cnf(c_14,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,k1_funct_1(X4,X1),k1_funct_1(X4,X2))
    | ~ sP0(X3,X4,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k1_funct_1(X4,X2),u1_struct_0(X3))
    | ~ m1_subset_1(k1_funct_1(X4,X1),u1_struct_0(X3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2449,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | r1_orders_2(X3,k1_funct_1(X4,X1),k1_funct_1(X4,X2)) = iProver_top
    | sP0(X3,X4,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k1_funct_1(X4,X2),u1_struct_0(X3)) != iProver_top
    | m1_subset_1(k1_funct_1(X4,X1),u1_struct_0(X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9549,plain,
    ( r1_orders_2(X0,k1_funct_1(X1,sK2(X2,X3,sK8)),k1_funct_1(X1,sK3(X2,X3,sK8))) = iProver_top
    | sP0(X0,X1,sK6) != iProver_top
    | sP0(X2,X3,sK8) = iProver_top
    | m1_subset_1(sK2(X2,X3,sK8),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK3(X2,X3,sK8),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k1_funct_1(X1,sK2(X2,X3,sK8)),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k1_funct_1(X1,sK3(X2,X3,sK8)),u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9542,c_2449])).

cnf(c_9562,plain,
    ( r1_orders_2(X0,k1_funct_1(X1,sK2(X2,X3,sK8)),k1_funct_1(X1,sK3(X2,X3,sK8))) = iProver_top
    | sP0(X0,X1,sK6) != iProver_top
    | sP0(X2,X3,sK8) = iProver_top
    | m1_subset_1(sK2(X2,X3,sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK3(X2,X3,sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k1_funct_1(X1,sK2(X2,X3,sK8)),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k1_funct_1(X1,sK3(X2,X3,sK8)),u1_struct_0(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9549,c_4901])).

cnf(c_2450,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9834,plain,
    ( r1_orders_2(X0,k1_funct_1(X1,sK2(X2,X3,sK8)),k1_funct_1(X1,sK3(X2,X3,sK8))) = iProver_top
    | sP0(X0,X1,sK6) != iProver_top
    | sP0(X2,X3,sK8) = iProver_top
    | m1_subset_1(k1_funct_1(X1,sK2(X2,X3,sK8)),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k1_funct_1(X1,sK3(X2,X3,sK8)),u1_struct_0(X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9562,c_2451,c_2450])).

cnf(c_9839,plain,
    ( r1_orders_2(X0,k1_funct_1(sK11,sK2(sK9,sK11,sK8)),sK5(sK9,sK11,sK8)) = iProver_top
    | sP0(X0,sK11,sK6) != iProver_top
    | sP0(sK9,sK11,sK8) = iProver_top
    | m1_subset_1(k1_funct_1(sK11,sK2(sK9,sK11,sK8)),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,sK3(sK9,sK11,sK8)),u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4462,c_9834])).

cnf(c_8,plain,
    ( sP0(X0,X1,X2)
    | k1_funct_1(X1,sK2(X0,X1,X2)) = sK4(X0,X1,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2455,plain,
    ( k1_funct_1(X0,sK2(X1,X0,X2)) = sK4(X1,X0,X2)
    | sP0(X1,X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3680,plain,
    ( k1_funct_1(sK11,sK2(sK9,sK11,sK8)) = sK4(sK9,sK11,sK8) ),
    inference(superposition,[status(thm)],[c_2455,c_2440])).

cnf(c_9876,plain,
    ( r1_orders_2(X0,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
    | sP0(X0,sK11,sK6) != iProver_top
    | sP0(sK9,sK11,sK8) = iProver_top
    | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9839,c_3680,c_4462])).

cnf(c_1053,plain,
    ( sP0(sK9,sK11,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1052])).

cnf(c_24141,plain,
    ( sP0(X0,sK11,sK6) != iProver_top
    | r1_orders_2(X0,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
    | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9876,c_1053])).

cnf(c_24142,plain,
    ( r1_orders_2(X0,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
    | sP0(X0,sK11,sK6) != iProver_top
    | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_24141])).

cnf(c_9,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2454,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2445,plain,
    ( l1_orders_2(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2936,plain,
    ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) = k7_lattice3(k7_lattice3(sK9)) ),
    inference(superposition,[status(thm)],[c_2445,c_2458])).

cnf(c_20,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2987,plain,
    ( g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = k7_lattice3(k7_lattice3(sK9)) ),
    inference(demodulation,[status(thm)],[c_2936,c_20])).

cnf(c_3376,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK9))
    | r1_orders_2(X0,X1,X2) = iProver_top
    | r1_orders_2(sK7,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2987,c_2448])).

cnf(c_30,negated_conjecture,
    ( l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_33,plain,
    ( l1_orders_2(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4037,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r1_orders_2(sK7,X1,X2) != iProver_top
    | r1_orders_2(X0,X1,X2) = iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3376,c_33])).

cnf(c_4038,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK9))
    | r1_orders_2(X0,X1,X2) = iProver_top
    | r1_orders_2(sK7,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4037])).

cnf(c_4052,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | r1_orders_2(sK9,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | l1_orders_2(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2936,c_4038])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2460,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5341,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK9))
    | u1_orders_2(sK7) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2987,c_2460])).

cnf(c_5345,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK9))
    | u1_orders_2(sK7) = X1
    | m1_subset_1(u1_orders_2(sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2987,c_2460])).

cnf(c_5410,plain,
    ( ~ m1_subset_1(u1_orders_2(sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7))))
    | g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK9))
    | u1_orders_2(sK7) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5345])).

cnf(c_5473,plain,
    ( m1_subset_1(u1_orders_2(sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7))))
    | ~ l1_orders_2(sK7) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5623,plain,
    ( u1_orders_2(sK7) = X1
    | g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5341,c_30,c_5410,c_5473])).

cnf(c_5624,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK9))
    | u1_orders_2(sK7) = X1 ),
    inference(renaming,[status(thm)],[c_5623])).

cnf(c_5629,plain,
    ( u1_orders_2(sK9) = u1_orders_2(sK7) ),
    inference(superposition,[status(thm)],[c_2936,c_5624])).

cnf(c_3373,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK9))
    | r1_orders_2(X0,X1,X2) != iProver_top
    | r1_orders_2(sK9,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2936,c_2448])).

cnf(c_35,plain,
    ( l1_orders_2(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5931,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r1_orders_2(sK9,X1,X2) = iProver_top
    | r1_orders_2(X0,X1,X2) != iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3373,c_35])).

cnf(c_5932,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK9))
    | r1_orders_2(X0,X1,X2) != iProver_top
    | r1_orders_2(sK9,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5931])).

cnf(c_5948,plain,
    ( g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK9)) != k7_lattice3(k7_lattice3(sK9))
    | r1_orders_2(sK7,X0,X1) != iProver_top
    | r1_orders_2(sK9,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | l1_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5629,c_5932])).

cnf(c_5654,plain,
    ( g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK9)) = k7_lattice3(k7_lattice3(sK9)) ),
    inference(demodulation,[status(thm)],[c_5629,c_2987])).

cnf(c_5957,plain,
    ( k7_lattice3(k7_lattice3(sK9)) != k7_lattice3(k7_lattice3(sK9))
    | r1_orders_2(sK7,X0,X1) != iProver_top
    | r1_orders_2(sK9,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | l1_orders_2(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5948,c_5654])).

cnf(c_5958,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | r1_orders_2(sK9,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | l1_orders_2(sK7) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5957])).

cnf(c_7284,plain,
    ( m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r1_orders_2(sK9,X0,X1) = iProver_top
    | r1_orders_2(sK7,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4052,c_33,c_5958])).

cnf(c_7285,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | r1_orders_2(sK9,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7284])).

cnf(c_4754,plain,
    ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK9))
    | u1_struct_0(sK7) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2987,c_2459])).

cnf(c_4840,plain,
    ( u1_struct_0(sK9) = u1_struct_0(sK7)
    | m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2936,c_4754])).

cnf(c_4221,plain,
    ( m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
    | ~ l1_orders_2(sK9) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4226,plain,
    ( m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)))) = iProver_top
    | l1_orders_2(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4221])).

cnf(c_6161,plain,
    ( u1_struct_0(sK9) = u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4840,c_35,c_4226])).

cnf(c_7290,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | r1_orders_2(sK9,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7285,c_6161])).

cnf(c_7298,plain,
    ( r1_orders_2(sK7,X0,sK5(sK9,X1,X2)) != iProver_top
    | r1_orders_2(sK9,X0,sK5(sK9,X1,X2)) = iProver_top
    | sP0(sK9,X1,X2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2454,c_7290])).

cnf(c_24154,plain,
    ( r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
    | sP0(sK7,sK11,sK6) != iProver_top
    | sP0(sK9,sK11,sK8) = iProver_top
    | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24142,c_7298])).

cnf(c_24172,plain,
    ( r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
    | sP0(sK7,sK11,sK6) != iProver_top
    | sP0(sK9,sK11,sK8) = iProver_top
    | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24154,c_6161])).

cnf(c_5,plain,
    ( ~ sP1(X0,X1,X2)
    | sP0(X2,X1,X0)
    | ~ v5_orders_3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,negated_conjecture,
    ( v5_orders_3(sK10,sK6,sK7) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_331,plain,
    ( ~ sP1(X0,X1,X2)
    | sP0(X2,X1,X0)
    | sK7 != X2
    | sK6 != X0
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_332,plain,
    ( ~ sP1(sK6,sK10,sK7)
    | sP0(sK7,sK10,sK6) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_469,plain,
    ( sP0(sK7,sK10,sK6)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK9)
    | u1_struct_0(X0) != u1_struct_0(sK8)
    | sK7 != X1
    | sK6 != X0
    | sK10 != sK11 ),
    inference(resolution_lifted,[status(thm)],[c_332,c_364])).

cnf(c_470,plain,
    ( sP0(sK7,sK10,sK6)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ l1_orders_2(sK7)
    | ~ l1_orders_2(sK6)
    | u1_struct_0(sK7) != u1_struct_0(sK9)
    | u1_struct_0(sK6) != u1_struct_0(sK8)
    | sK10 != sK11 ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_19,negated_conjecture,
    ( sK10 = sK11 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_472,plain,
    ( u1_struct_0(sK6) != u1_struct_0(sK8)
    | u1_struct_0(sK7) != u1_struct_0(sK9)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | sP0(sK7,sK10,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_470,c_31,c_30,c_19])).

cnf(c_473,plain,
    ( sP0(sK7,sK10,sK6)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | u1_struct_0(sK7) != u1_struct_0(sK9)
    | u1_struct_0(sK6) != u1_struct_0(sK8) ),
    inference(renaming,[status(thm)],[c_472])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_388,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
    | ~ v1_funct_1(X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X2)
    | u1_struct_0(X2) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_389,plain,
    ( sP1(X0,sK10,X1)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK10)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_393,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | sP1(X0,sK10,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_27])).

cnf(c_394,plain,
    ( sP1(X0,sK10,X1)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6) ),
    inference(renaming,[status(thm)],[c_393])).

cnf(c_489,plain,
    ( sP0(sK7,sK10,sK6)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | sK7 != X1
    | sK6 != X0
    | sK10 != sK10 ),
    inference(resolution_lifted,[status(thm)],[c_332,c_394])).

cnf(c_490,plain,
    ( sP0(sK7,sK10,sK6)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ l1_orders_2(sK7)
    | ~ l1_orders_2(sK6)
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_492,plain,
    ( sP0(sK7,sK10,sK6)
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_490,c_31,c_30,c_25])).

cnf(c_1044,plain,
    ( sP0(sK7,sK10,sK6) ),
    inference(equality_resolution_simp,[status(thm)],[c_492])).

cnf(c_1047,plain,
    ( sP0(sK7,sK10,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_1044])).

cnf(c_2441,plain,
    ( sP0(sK7,sK10,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1047])).

cnf(c_2472,plain,
    ( sP0(sK7,sK11,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2441,c_19])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2))
    | sP0(X0,X1,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_863,plain,
    ( ~ r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2))
    | u1_struct_0(sK9) != u1_struct_0(sK9)
    | u1_struct_0(sK8) != u1_struct_0(sK8)
    | sK9 != X0
    | sK8 != X2
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_435])).

cnf(c_864,plain,
    ( ~ r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) ),
    inference(unflattening,[status(thm)],[c_863])).

cnf(c_865,plain,
    ( r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_864])).

cnf(c_798,plain,
    ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
    | u1_struct_0(sK9) != u1_struct_0(sK9)
    | u1_struct_0(sK8) != u1_struct_0(sK8)
    | sK9 != X0
    | sK8 != X2
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_435])).

cnf(c_799,plain,
    ( m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) ),
    inference(unflattening,[status(thm)],[c_798])).

cnf(c_800,plain,
    ( m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_10,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_775,plain,
    ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
    | u1_struct_0(sK9) != u1_struct_0(sK9)
    | u1_struct_0(sK8) != u1_struct_0(sK8)
    | sK9 != X0
    | sK8 != X2
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_435])).

cnf(c_776,plain,
    ( m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_777,plain,
    ( m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_776])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24172,c_2472,c_1053,c_865,c_800,c_777])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:31:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.03/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.03/1.49  
% 7.03/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.03/1.49  
% 7.03/1.49  ------  iProver source info
% 7.03/1.49  
% 7.03/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.03/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.03/1.49  git: non_committed_changes: false
% 7.03/1.49  git: last_make_outside_of_git: false
% 7.03/1.49  
% 7.03/1.49  ------ 
% 7.03/1.49  
% 7.03/1.49  ------ Input Options
% 7.03/1.49  
% 7.03/1.49  --out_options                           all
% 7.03/1.49  --tptp_safe_out                         true
% 7.03/1.49  --problem_path                          ""
% 7.03/1.49  --include_path                          ""
% 7.03/1.49  --clausifier                            res/vclausify_rel
% 7.03/1.49  --clausifier_options                    --mode clausify
% 7.03/1.49  --stdin                                 false
% 7.03/1.49  --stats_out                             all
% 7.03/1.49  
% 7.03/1.49  ------ General Options
% 7.03/1.49  
% 7.03/1.49  --fof                                   false
% 7.03/1.49  --time_out_real                         305.
% 7.03/1.49  --time_out_virtual                      -1.
% 7.03/1.49  --symbol_type_check                     false
% 7.03/1.49  --clausify_out                          false
% 7.03/1.49  --sig_cnt_out                           false
% 7.03/1.49  --trig_cnt_out                          false
% 7.03/1.49  --trig_cnt_out_tolerance                1.
% 7.03/1.49  --trig_cnt_out_sk_spl                   false
% 7.03/1.49  --abstr_cl_out                          false
% 7.03/1.49  
% 7.03/1.49  ------ Global Options
% 7.03/1.49  
% 7.03/1.49  --schedule                              default
% 7.03/1.49  --add_important_lit                     false
% 7.03/1.49  --prop_solver_per_cl                    1000
% 7.03/1.49  --min_unsat_core                        false
% 7.03/1.49  --soft_assumptions                      false
% 7.03/1.49  --soft_lemma_size                       3
% 7.03/1.49  --prop_impl_unit_size                   0
% 7.03/1.49  --prop_impl_unit                        []
% 7.03/1.49  --share_sel_clauses                     true
% 7.03/1.49  --reset_solvers                         false
% 7.03/1.49  --bc_imp_inh                            [conj_cone]
% 7.03/1.49  --conj_cone_tolerance                   3.
% 7.03/1.49  --extra_neg_conj                        none
% 7.03/1.49  --large_theory_mode                     true
% 7.03/1.49  --prolific_symb_bound                   200
% 7.03/1.49  --lt_threshold                          2000
% 7.03/1.49  --clause_weak_htbl                      true
% 7.03/1.49  --gc_record_bc_elim                     false
% 7.03/1.49  
% 7.03/1.49  ------ Preprocessing Options
% 7.03/1.49  
% 7.03/1.49  --preprocessing_flag                    true
% 7.03/1.49  --time_out_prep_mult                    0.1
% 7.03/1.49  --splitting_mode                        input
% 7.03/1.49  --splitting_grd                         true
% 7.03/1.49  --splitting_cvd                         false
% 7.03/1.49  --splitting_cvd_svl                     false
% 7.03/1.49  --splitting_nvd                         32
% 7.03/1.49  --sub_typing                            true
% 7.03/1.49  --prep_gs_sim                           true
% 7.03/1.49  --prep_unflatten                        true
% 7.03/1.49  --prep_res_sim                          true
% 7.03/1.49  --prep_upred                            true
% 7.03/1.49  --prep_sem_filter                       exhaustive
% 7.03/1.49  --prep_sem_filter_out                   false
% 7.03/1.49  --pred_elim                             true
% 7.03/1.49  --res_sim_input                         true
% 7.03/1.49  --eq_ax_congr_red                       true
% 7.03/1.49  --pure_diseq_elim                       true
% 7.03/1.49  --brand_transform                       false
% 7.03/1.49  --non_eq_to_eq                          false
% 7.03/1.49  --prep_def_merge                        true
% 7.03/1.49  --prep_def_merge_prop_impl              false
% 7.03/1.49  --prep_def_merge_mbd                    true
% 7.03/1.49  --prep_def_merge_tr_red                 false
% 7.03/1.49  --prep_def_merge_tr_cl                  false
% 7.03/1.49  --smt_preprocessing                     true
% 7.03/1.49  --smt_ac_axioms                         fast
% 7.03/1.49  --preprocessed_out                      false
% 7.03/1.49  --preprocessed_stats                    false
% 7.03/1.49  
% 7.03/1.49  ------ Abstraction refinement Options
% 7.03/1.49  
% 7.03/1.49  --abstr_ref                             []
% 7.03/1.49  --abstr_ref_prep                        false
% 7.03/1.49  --abstr_ref_until_sat                   false
% 7.03/1.49  --abstr_ref_sig_restrict                funpre
% 7.03/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.03/1.49  --abstr_ref_under                       []
% 7.03/1.49  
% 7.03/1.49  ------ SAT Options
% 7.03/1.49  
% 7.03/1.49  --sat_mode                              false
% 7.03/1.49  --sat_fm_restart_options                ""
% 7.03/1.49  --sat_gr_def                            false
% 7.03/1.49  --sat_epr_types                         true
% 7.03/1.49  --sat_non_cyclic_types                  false
% 7.03/1.49  --sat_finite_models                     false
% 7.03/1.49  --sat_fm_lemmas                         false
% 7.03/1.49  --sat_fm_prep                           false
% 7.03/1.49  --sat_fm_uc_incr                        true
% 7.03/1.49  --sat_out_model                         small
% 7.03/1.49  --sat_out_clauses                       false
% 7.03/1.49  
% 7.03/1.49  ------ QBF Options
% 7.03/1.49  
% 7.03/1.49  --qbf_mode                              false
% 7.03/1.49  --qbf_elim_univ                         false
% 7.03/1.49  --qbf_dom_inst                          none
% 7.03/1.49  --qbf_dom_pre_inst                      false
% 7.03/1.49  --qbf_sk_in                             false
% 7.03/1.49  --qbf_pred_elim                         true
% 7.03/1.49  --qbf_split                             512
% 7.03/1.49  
% 7.03/1.49  ------ BMC1 Options
% 7.03/1.49  
% 7.03/1.49  --bmc1_incremental                      false
% 7.03/1.49  --bmc1_axioms                           reachable_all
% 7.03/1.49  --bmc1_min_bound                        0
% 7.03/1.49  --bmc1_max_bound                        -1
% 7.03/1.49  --bmc1_max_bound_default                -1
% 7.03/1.49  --bmc1_symbol_reachability              true
% 7.03/1.49  --bmc1_property_lemmas                  false
% 7.03/1.49  --bmc1_k_induction                      false
% 7.03/1.49  --bmc1_non_equiv_states                 false
% 7.03/1.49  --bmc1_deadlock                         false
% 7.03/1.49  --bmc1_ucm                              false
% 7.03/1.49  --bmc1_add_unsat_core                   none
% 7.03/1.49  --bmc1_unsat_core_children              false
% 7.03/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.03/1.49  --bmc1_out_stat                         full
% 7.03/1.49  --bmc1_ground_init                      false
% 7.03/1.49  --bmc1_pre_inst_next_state              false
% 7.03/1.49  --bmc1_pre_inst_state                   false
% 7.03/1.49  --bmc1_pre_inst_reach_state             false
% 7.03/1.49  --bmc1_out_unsat_core                   false
% 7.03/1.49  --bmc1_aig_witness_out                  false
% 7.03/1.49  --bmc1_verbose                          false
% 7.03/1.49  --bmc1_dump_clauses_tptp                false
% 7.03/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.03/1.49  --bmc1_dump_file                        -
% 7.03/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.03/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.03/1.49  --bmc1_ucm_extend_mode                  1
% 7.03/1.49  --bmc1_ucm_init_mode                    2
% 7.03/1.49  --bmc1_ucm_cone_mode                    none
% 7.03/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.03/1.49  --bmc1_ucm_relax_model                  4
% 7.03/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.03/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.03/1.49  --bmc1_ucm_layered_model                none
% 7.03/1.49  --bmc1_ucm_max_lemma_size               10
% 7.03/1.49  
% 7.03/1.49  ------ AIG Options
% 7.03/1.49  
% 7.03/1.49  --aig_mode                              false
% 7.03/1.49  
% 7.03/1.49  ------ Instantiation Options
% 7.03/1.49  
% 7.03/1.49  --instantiation_flag                    true
% 7.03/1.49  --inst_sos_flag                         false
% 7.03/1.49  --inst_sos_phase                        true
% 7.03/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.03/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.03/1.49  --inst_lit_sel_side                     num_symb
% 7.03/1.49  --inst_solver_per_active                1400
% 7.03/1.49  --inst_solver_calls_frac                1.
% 7.03/1.49  --inst_passive_queue_type               priority_queues
% 7.03/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.03/1.49  --inst_passive_queues_freq              [25;2]
% 7.03/1.49  --inst_dismatching                      true
% 7.03/1.49  --inst_eager_unprocessed_to_passive     true
% 7.03/1.49  --inst_prop_sim_given                   true
% 7.03/1.49  --inst_prop_sim_new                     false
% 7.03/1.49  --inst_subs_new                         false
% 7.03/1.49  --inst_eq_res_simp                      false
% 7.03/1.49  --inst_subs_given                       false
% 7.03/1.49  --inst_orphan_elimination               true
% 7.03/1.49  --inst_learning_loop_flag               true
% 7.03/1.49  --inst_learning_start                   3000
% 7.03/1.49  --inst_learning_factor                  2
% 7.03/1.49  --inst_start_prop_sim_after_learn       3
% 7.03/1.49  --inst_sel_renew                        solver
% 7.03/1.49  --inst_lit_activity_flag                true
% 7.03/1.49  --inst_restr_to_given                   false
% 7.03/1.49  --inst_activity_threshold               500
% 7.03/1.49  --inst_out_proof                        true
% 7.03/1.49  
% 7.03/1.49  ------ Resolution Options
% 7.03/1.49  
% 7.03/1.49  --resolution_flag                       true
% 7.03/1.49  --res_lit_sel                           adaptive
% 7.03/1.49  --res_lit_sel_side                      none
% 7.03/1.49  --res_ordering                          kbo
% 7.03/1.49  --res_to_prop_solver                    active
% 7.03/1.49  --res_prop_simpl_new                    false
% 7.03/1.49  --res_prop_simpl_given                  true
% 7.03/1.49  --res_passive_queue_type                priority_queues
% 7.03/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.03/1.49  --res_passive_queues_freq               [15;5]
% 7.03/1.49  --res_forward_subs                      full
% 7.03/1.49  --res_backward_subs                     full
% 7.03/1.49  --res_forward_subs_resolution           true
% 7.03/1.49  --res_backward_subs_resolution          true
% 7.03/1.49  --res_orphan_elimination                true
% 7.03/1.49  --res_time_limit                        2.
% 7.03/1.49  --res_out_proof                         true
% 7.03/1.49  
% 7.03/1.49  ------ Superposition Options
% 7.03/1.49  
% 7.03/1.49  --superposition_flag                    true
% 7.03/1.49  --sup_passive_queue_type                priority_queues
% 7.03/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.03/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.03/1.49  --demod_completeness_check              fast
% 7.03/1.49  --demod_use_ground                      true
% 7.03/1.49  --sup_to_prop_solver                    passive
% 7.03/1.49  --sup_prop_simpl_new                    true
% 7.03/1.49  --sup_prop_simpl_given                  true
% 7.03/1.49  --sup_fun_splitting                     false
% 7.03/1.49  --sup_smt_interval                      50000
% 7.03/1.49  
% 7.03/1.49  ------ Superposition Simplification Setup
% 7.03/1.49  
% 7.03/1.49  --sup_indices_passive                   []
% 7.03/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.03/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.03/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.03/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.03/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.03/1.49  --sup_full_bw                           [BwDemod]
% 7.03/1.49  --sup_immed_triv                        [TrivRules]
% 7.03/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.03/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.03/1.49  --sup_immed_bw_main                     []
% 7.03/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.03/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.03/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.03/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.03/1.49  
% 7.03/1.49  ------ Combination Options
% 7.03/1.49  
% 7.03/1.49  --comb_res_mult                         3
% 7.03/1.49  --comb_sup_mult                         2
% 7.03/1.49  --comb_inst_mult                        10
% 7.03/1.49  
% 7.03/1.49  ------ Debug Options
% 7.03/1.49  
% 7.03/1.49  --dbg_backtrace                         false
% 7.03/1.49  --dbg_dump_prop_clauses                 false
% 7.03/1.49  --dbg_dump_prop_clauses_file            -
% 7.03/1.49  --dbg_out_stat                          false
% 7.03/1.49  ------ Parsing...
% 7.03/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.03/1.49  
% 7.03/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.03/1.49  
% 7.03/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.03/1.49  
% 7.03/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.03/1.49  ------ Proving...
% 7.03/1.49  ------ Problem Properties 
% 7.03/1.49  
% 7.03/1.49  
% 7.03/1.49  clauses                                 26
% 7.03/1.49  conjectures                             9
% 7.03/1.49  EPR                                     8
% 7.03/1.49  Horn                                    19
% 7.03/1.49  unary                                   11
% 7.03/1.49  binary                                  11
% 7.03/1.49  lits                                    55
% 7.03/1.49  lits eq                                 13
% 7.03/1.49  fd_pure                                 0
% 7.03/1.49  fd_pseudo                               0
% 7.03/1.49  fd_cond                                 0
% 7.03/1.49  fd_pseudo_cond                          2
% 7.03/1.49  AC symbols                              0
% 7.03/1.49  
% 7.03/1.49  ------ Schedule dynamic 5 is on 
% 7.03/1.49  
% 7.03/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.03/1.49  
% 7.03/1.49  
% 7.03/1.49  ------ 
% 7.03/1.49  Current options:
% 7.03/1.49  ------ 
% 7.03/1.49  
% 7.03/1.49  ------ Input Options
% 7.03/1.49  
% 7.03/1.49  --out_options                           all
% 7.03/1.49  --tptp_safe_out                         true
% 7.03/1.49  --problem_path                          ""
% 7.03/1.49  --include_path                          ""
% 7.03/1.49  --clausifier                            res/vclausify_rel
% 7.03/1.49  --clausifier_options                    --mode clausify
% 7.03/1.49  --stdin                                 false
% 7.03/1.49  --stats_out                             all
% 7.03/1.49  
% 7.03/1.49  ------ General Options
% 7.03/1.49  
% 7.03/1.49  --fof                                   false
% 7.03/1.49  --time_out_real                         305.
% 7.03/1.49  --time_out_virtual                      -1.
% 7.03/1.49  --symbol_type_check                     false
% 7.03/1.49  --clausify_out                          false
% 7.03/1.49  --sig_cnt_out                           false
% 7.03/1.49  --trig_cnt_out                          false
% 7.03/1.49  --trig_cnt_out_tolerance                1.
% 7.03/1.49  --trig_cnt_out_sk_spl                   false
% 7.03/1.49  --abstr_cl_out                          false
% 7.03/1.49  
% 7.03/1.49  ------ Global Options
% 7.03/1.49  
% 7.03/1.49  --schedule                              default
% 7.03/1.49  --add_important_lit                     false
% 7.03/1.49  --prop_solver_per_cl                    1000
% 7.03/1.49  --min_unsat_core                        false
% 7.03/1.49  --soft_assumptions                      false
% 7.03/1.49  --soft_lemma_size                       3
% 7.03/1.49  --prop_impl_unit_size                   0
% 7.03/1.49  --prop_impl_unit                        []
% 7.03/1.49  --share_sel_clauses                     true
% 7.03/1.49  --reset_solvers                         false
% 7.03/1.49  --bc_imp_inh                            [conj_cone]
% 7.03/1.49  --conj_cone_tolerance                   3.
% 7.03/1.49  --extra_neg_conj                        none
% 7.03/1.49  --large_theory_mode                     true
% 7.03/1.49  --prolific_symb_bound                   200
% 7.03/1.49  --lt_threshold                          2000
% 7.03/1.49  --clause_weak_htbl                      true
% 7.03/1.49  --gc_record_bc_elim                     false
% 7.03/1.49  
% 7.03/1.49  ------ Preprocessing Options
% 7.03/1.49  
% 7.03/1.49  --preprocessing_flag                    true
% 7.03/1.49  --time_out_prep_mult                    0.1
% 7.03/1.49  --splitting_mode                        input
% 7.03/1.49  --splitting_grd                         true
% 7.03/1.49  --splitting_cvd                         false
% 7.03/1.49  --splitting_cvd_svl                     false
% 7.03/1.49  --splitting_nvd                         32
% 7.03/1.49  --sub_typing                            true
% 7.03/1.49  --prep_gs_sim                           true
% 7.03/1.49  --prep_unflatten                        true
% 7.03/1.49  --prep_res_sim                          true
% 7.03/1.49  --prep_upred                            true
% 7.03/1.49  --prep_sem_filter                       exhaustive
% 7.03/1.49  --prep_sem_filter_out                   false
% 7.03/1.49  --pred_elim                             true
% 7.03/1.49  --res_sim_input                         true
% 7.03/1.49  --eq_ax_congr_red                       true
% 7.03/1.49  --pure_diseq_elim                       true
% 7.03/1.49  --brand_transform                       false
% 7.03/1.49  --non_eq_to_eq                          false
% 7.03/1.49  --prep_def_merge                        true
% 7.03/1.49  --prep_def_merge_prop_impl              false
% 7.03/1.49  --prep_def_merge_mbd                    true
% 7.03/1.49  --prep_def_merge_tr_red                 false
% 7.03/1.49  --prep_def_merge_tr_cl                  false
% 7.03/1.49  --smt_preprocessing                     true
% 7.03/1.49  --smt_ac_axioms                         fast
% 7.03/1.49  --preprocessed_out                      false
% 7.03/1.49  --preprocessed_stats                    false
% 7.03/1.49  
% 7.03/1.49  ------ Abstraction refinement Options
% 7.03/1.49  
% 7.03/1.49  --abstr_ref                             []
% 7.03/1.49  --abstr_ref_prep                        false
% 7.03/1.49  --abstr_ref_until_sat                   false
% 7.03/1.49  --abstr_ref_sig_restrict                funpre
% 7.03/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.03/1.49  --abstr_ref_under                       []
% 7.03/1.49  
% 7.03/1.49  ------ SAT Options
% 7.03/1.49  
% 7.03/1.49  --sat_mode                              false
% 7.03/1.49  --sat_fm_restart_options                ""
% 7.03/1.49  --sat_gr_def                            false
% 7.03/1.49  --sat_epr_types                         true
% 7.03/1.49  --sat_non_cyclic_types                  false
% 7.03/1.49  --sat_finite_models                     false
% 7.03/1.49  --sat_fm_lemmas                         false
% 7.03/1.49  --sat_fm_prep                           false
% 7.03/1.49  --sat_fm_uc_incr                        true
% 7.03/1.49  --sat_out_model                         small
% 7.03/1.49  --sat_out_clauses                       false
% 7.03/1.49  
% 7.03/1.49  ------ QBF Options
% 7.03/1.49  
% 7.03/1.49  --qbf_mode                              false
% 7.03/1.49  --qbf_elim_univ                         false
% 7.03/1.49  --qbf_dom_inst                          none
% 7.03/1.49  --qbf_dom_pre_inst                      false
% 7.03/1.49  --qbf_sk_in                             false
% 7.03/1.49  --qbf_pred_elim                         true
% 7.03/1.49  --qbf_split                             512
% 7.03/1.49  
% 7.03/1.49  ------ BMC1 Options
% 7.03/1.49  
% 7.03/1.49  --bmc1_incremental                      false
% 7.03/1.49  --bmc1_axioms                           reachable_all
% 7.03/1.49  --bmc1_min_bound                        0
% 7.03/1.49  --bmc1_max_bound                        -1
% 7.03/1.49  --bmc1_max_bound_default                -1
% 7.03/1.49  --bmc1_symbol_reachability              true
% 7.03/1.49  --bmc1_property_lemmas                  false
% 7.03/1.49  --bmc1_k_induction                      false
% 7.03/1.49  --bmc1_non_equiv_states                 false
% 7.03/1.49  --bmc1_deadlock                         false
% 7.03/1.49  --bmc1_ucm                              false
% 7.03/1.49  --bmc1_add_unsat_core                   none
% 7.03/1.49  --bmc1_unsat_core_children              false
% 7.03/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.03/1.49  --bmc1_out_stat                         full
% 7.03/1.49  --bmc1_ground_init                      false
% 7.03/1.49  --bmc1_pre_inst_next_state              false
% 7.03/1.49  --bmc1_pre_inst_state                   false
% 7.03/1.49  --bmc1_pre_inst_reach_state             false
% 7.03/1.49  --bmc1_out_unsat_core                   false
% 7.03/1.49  --bmc1_aig_witness_out                  false
% 7.03/1.49  --bmc1_verbose                          false
% 7.03/1.49  --bmc1_dump_clauses_tptp                false
% 7.03/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.03/1.49  --bmc1_dump_file                        -
% 7.03/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.03/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.03/1.49  --bmc1_ucm_extend_mode                  1
% 7.03/1.49  --bmc1_ucm_init_mode                    2
% 7.03/1.49  --bmc1_ucm_cone_mode                    none
% 7.03/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.03/1.49  --bmc1_ucm_relax_model                  4
% 7.03/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.03/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.03/1.49  --bmc1_ucm_layered_model                none
% 7.03/1.49  --bmc1_ucm_max_lemma_size               10
% 7.03/1.49  
% 7.03/1.49  ------ AIG Options
% 7.03/1.49  
% 7.03/1.49  --aig_mode                              false
% 7.03/1.49  
% 7.03/1.49  ------ Instantiation Options
% 7.03/1.49  
% 7.03/1.49  --instantiation_flag                    true
% 7.03/1.49  --inst_sos_flag                         false
% 7.03/1.49  --inst_sos_phase                        true
% 7.03/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.03/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.03/1.49  --inst_lit_sel_side                     none
% 7.03/1.49  --inst_solver_per_active                1400
% 7.03/1.49  --inst_solver_calls_frac                1.
% 7.03/1.49  --inst_passive_queue_type               priority_queues
% 7.03/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.03/1.49  --inst_passive_queues_freq              [25;2]
% 7.03/1.49  --inst_dismatching                      true
% 7.03/1.49  --inst_eager_unprocessed_to_passive     true
% 7.03/1.49  --inst_prop_sim_given                   true
% 7.03/1.49  --inst_prop_sim_new                     false
% 7.03/1.49  --inst_subs_new                         false
% 7.03/1.49  --inst_eq_res_simp                      false
% 7.03/1.49  --inst_subs_given                       false
% 7.03/1.49  --inst_orphan_elimination               true
% 7.03/1.49  --inst_learning_loop_flag               true
% 7.03/1.49  --inst_learning_start                   3000
% 7.03/1.49  --inst_learning_factor                  2
% 7.03/1.49  --inst_start_prop_sim_after_learn       3
% 7.03/1.49  --inst_sel_renew                        solver
% 7.03/1.49  --inst_lit_activity_flag                true
% 7.03/1.49  --inst_restr_to_given                   false
% 7.03/1.49  --inst_activity_threshold               500
% 7.03/1.49  --inst_out_proof                        true
% 7.03/1.49  
% 7.03/1.49  ------ Resolution Options
% 7.03/1.49  
% 7.03/1.49  --resolution_flag                       false
% 7.03/1.49  --res_lit_sel                           adaptive
% 7.03/1.49  --res_lit_sel_side                      none
% 7.03/1.49  --res_ordering                          kbo
% 7.03/1.49  --res_to_prop_solver                    active
% 7.03/1.49  --res_prop_simpl_new                    false
% 7.03/1.49  --res_prop_simpl_given                  true
% 7.03/1.49  --res_passive_queue_type                priority_queues
% 7.03/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.03/1.49  --res_passive_queues_freq               [15;5]
% 7.03/1.49  --res_forward_subs                      full
% 7.03/1.49  --res_backward_subs                     full
% 7.03/1.49  --res_forward_subs_resolution           true
% 7.03/1.49  --res_backward_subs_resolution          true
% 7.03/1.49  --res_orphan_elimination                true
% 7.03/1.49  --res_time_limit                        2.
% 7.03/1.49  --res_out_proof                         true
% 7.03/1.49  
% 7.03/1.49  ------ Superposition Options
% 7.03/1.49  
% 7.03/1.49  --superposition_flag                    true
% 7.03/1.49  --sup_passive_queue_type                priority_queues
% 7.03/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.03/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.03/1.49  --demod_completeness_check              fast
% 7.03/1.49  --demod_use_ground                      true
% 7.03/1.49  --sup_to_prop_solver                    passive
% 7.03/1.49  --sup_prop_simpl_new                    true
% 7.03/1.49  --sup_prop_simpl_given                  true
% 7.03/1.49  --sup_fun_splitting                     false
% 7.03/1.49  --sup_smt_interval                      50000
% 7.03/1.49  
% 7.03/1.49  ------ Superposition Simplification Setup
% 7.03/1.49  
% 7.03/1.49  --sup_indices_passive                   []
% 7.03/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.03/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.03/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.03/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.03/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.03/1.49  --sup_full_bw                           [BwDemod]
% 7.03/1.49  --sup_immed_triv                        [TrivRules]
% 7.03/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.03/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.03/1.49  --sup_immed_bw_main                     []
% 7.03/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.03/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.03/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.03/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.03/1.49  
% 7.03/1.49  ------ Combination Options
% 7.03/1.49  
% 7.03/1.49  --comb_res_mult                         3
% 7.03/1.49  --comb_sup_mult                         2
% 7.03/1.49  --comb_inst_mult                        10
% 7.03/1.49  
% 7.03/1.49  ------ Debug Options
% 7.03/1.49  
% 7.03/1.49  --dbg_backtrace                         false
% 7.03/1.49  --dbg_dump_prop_clauses                 false
% 7.03/1.49  --dbg_dump_prop_clauses_file            -
% 7.03/1.49  --dbg_out_stat                          false
% 7.03/1.49  
% 7.03/1.49  
% 7.03/1.49  
% 7.03/1.49  
% 7.03/1.49  ------ Proving...
% 7.03/1.49  
% 7.03/1.49  
% 7.03/1.49  % SZS status Theorem for theBenchmark.p
% 7.03/1.49  
% 7.03/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.03/1.49  
% 7.03/1.49  fof(f18,plain,(
% 7.03/1.49    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 7.03/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.03/1.49  
% 7.03/1.49  fof(f23,plain,(
% 7.03/1.49    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X5,X6) & k1_funct_1(X2,X4) = X6 & k1_funct_1(X2,X3) = X5 & m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X2,X0)))),
% 7.03/1.49    inference(nnf_transformation,[],[f18])).
% 7.03/1.49  
% 7.03/1.49  fof(f24,plain,(
% 7.03/1.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,X3,X4) & m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X2)))) & (! [X7] : (! [X8] : (! [X9] : (! [X10] : (r1_orders_2(X0,X9,X10) | k1_funct_1(X1,X8) != X10 | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X0))) | ~m1_subset_1(X9,u1_struct_0(X0))) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~sP0(X0,X1,X2)))),
% 7.03/1.49    inference(rectify,[],[f23])).
% 7.03/1.49  
% 7.03/1.49  fof(f28,plain,(
% 7.03/1.49    ( ! [X4,X5,X3] : (! [X2,X1,X0] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) => (~r1_orders_2(X0,X5,sK5(X0,X1,X2)) & k1_funct_1(X1,X4) = sK5(X0,X1,X2) & k1_funct_1(X1,X3) = X5 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))) )),
% 7.03/1.49    introduced(choice_axiom,[])).
% 7.03/1.49  
% 7.03/1.49  fof(f27,plain,(
% 7.03/1.49    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) => (? [X6] : (~r1_orders_2(X0,sK4(X0,X1,X2),X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = sK4(X0,X1,X2) & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))) )),
% 7.03/1.49    introduced(choice_axiom,[])).
% 7.03/1.49  
% 7.03/1.49  fof(f26,plain,(
% 7.03/1.49    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,X3,X4) & m1_subset_1(X4,u1_struct_0(X2))) => (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,sK3(X0,X1,X2)) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,X3,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2))))) )),
% 7.03/1.49    introduced(choice_axiom,[])).
% 7.03/1.49  
% 7.03/1.49  fof(f25,plain,(
% 7.03/1.49    ! [X2,X1,X0] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,X3,X4) & m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X2))) => (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,sK2(X0,X1,X2)) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,sK2(X0,X1,X2),X4) & m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2))))),
% 7.03/1.49    introduced(choice_axiom,[])).
% 7.03/1.49  
% 7.03/1.49  fof(f29,plain,(
% 7.03/1.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((((~r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2)) & k1_funct_1(X1,sK3(X0,X1,X2)) = sK5(X0,X1,X2) & k1_funct_1(X1,sK2(X0,X1,X2)) = sK4(X0,X1,X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) & r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)))) & (! [X7] : (! [X8] : (! [X9] : (! [X10] : (r1_orders_2(X0,X9,X10) | k1_funct_1(X1,X8) != X10 | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X0))) | ~m1_subset_1(X9,u1_struct_0(X0))) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~sP0(X0,X1,X2)))),
% 7.03/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f28,f27,f26,f25])).
% 7.03/1.49  
% 7.03/1.49  fof(f50,plain,(
% 7.03/1.49    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | k1_funct_1(X1,sK3(X0,X1,X2)) = sK5(X0,X1,X2)) )),
% 7.03/1.49    inference(cnf_transformation,[],[f29])).
% 7.03/1.49  
% 7.03/1.49  fof(f19,plain,(
% 7.03/1.49    ! [X0,X2,X1] : ((v5_orders_3(X2,X0,X1) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 7.03/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.03/1.49  
% 7.03/1.49  fof(f21,plain,(
% 7.03/1.49    ! [X0,X2,X1] : (((v5_orders_3(X2,X0,X1) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~v5_orders_3(X2,X0,X1))) | ~sP1(X0,X2,X1))),
% 7.03/1.49    inference(nnf_transformation,[],[f19])).
% 7.03/1.49  
% 7.03/1.49  fof(f22,plain,(
% 7.03/1.49    ! [X0,X1,X2] : (((v5_orders_3(X1,X0,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v5_orders_3(X1,X0,X2))) | ~sP1(X0,X1,X2))),
% 7.03/1.49    inference(rectify,[],[f21])).
% 7.03/1.49  
% 7.03/1.49  fof(f42,plain,(
% 7.03/1.49    ( ! [X2,X0,X1] : (v5_orders_3(X1,X0,X2) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 7.03/1.49    inference(cnf_transformation,[],[f22])).
% 7.03/1.49  
% 7.03/1.49  fof(f6,conjecture,(
% 7.03/1.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((l1_orders_2(X2) & ~v2_struct_0(X2)) => ! [X3] : ((l1_orders_2(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 7.03/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.03/1.49  
% 7.03/1.49  fof(f7,negated_conjecture,(
% 7.03/1.49    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((l1_orders_2(X2) & ~v2_struct_0(X2)) => ! [X3] : ((l1_orders_2(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 7.03/1.49    inference(negated_conjecture,[],[f6])).
% 7.03/1.49  
% 7.03/1.49  fof(f8,plain,(
% 7.03/1.49    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : (l1_orders_2(X2) => ! [X3] : (l1_orders_2(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 7.03/1.49    inference(pure_predicate_removal,[],[f7])).
% 7.03/1.49  
% 7.03/1.49  fof(f16,plain,(
% 7.03/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~v5_orders_3(X5,X2,X3) & (v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 7.03/1.49    inference(ennf_transformation,[],[f8])).
% 7.03/1.49  
% 7.03/1.49  fof(f17,plain,(
% 7.03/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 7.03/1.49    inference(flattening,[],[f16])).
% 7.03/1.49  
% 7.03/1.49  fof(f35,plain,(
% 7.03/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => (~v5_orders_3(sK11,X2,X3) & v5_orders_3(X4,X0,X1) & sK11 = X4 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(sK11,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(sK11))) )),
% 7.03/1.49    introduced(choice_axiom,[])).
% 7.03/1.49  
% 7.03/1.49  fof(f34,plain,(
% 7.03/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(sK10,X0,X1) & sK10 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK10,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK10))) )),
% 7.03/1.49    introduced(choice_axiom,[])).
% 7.03/1.49  
% 7.03/1.49  fof(f33,plain,(
% 7.03/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) => (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,sK9) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK9)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK9)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(sK9))) )),
% 7.03/1.49    introduced(choice_axiom,[])).
% 7.03/1.49  
% 7.03/1.49  fof(f32,plain,(
% 7.03/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) => (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,sK8,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(sK8))) )),
% 7.03/1.49    introduced(choice_axiom,[])).
% 7.03/1.49  
% 7.03/1.49  fof(f31,plain,(
% 7.03/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,sK7) & X4 = X5 & g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK7)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(sK7))) )),
% 7.03/1.49    introduced(choice_axiom,[])).
% 7.03/1.49  
% 7.03/1.49  fof(f30,plain,(
% 7.03/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,sK6,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(sK6))),
% 7.03/1.49    introduced(choice_axiom,[])).
% 7.03/1.49  
% 7.03/1.49  fof(f36,plain,(
% 7.03/1.49    (((((~v5_orders_3(sK11,sK8,sK9) & v5_orders_3(sK10,sK6,sK7) & sK10 = sK11 & g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) & g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) & v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) & v1_funct_1(sK11)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(sK10)) & l1_orders_2(sK9)) & l1_orders_2(sK8)) & l1_orders_2(sK7)) & l1_orders_2(sK6)),
% 7.03/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f17,f35,f34,f33,f32,f31,f30])).
% 7.03/1.49  
% 7.03/1.49  fof(f68,plain,(
% 7.03/1.49    ~v5_orders_3(sK11,sK8,sK9)),
% 7.03/1.49    inference(cnf_transformation,[],[f36])).
% 7.03/1.49  
% 7.03/1.49  fof(f4,axiom,(
% 7.03/1.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_orders_3(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_orders_2(X0,X3,X4) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X1)) => ((k1_funct_1(X2,X4) = X6 & k1_funct_1(X2,X3) = X5) => r1_orders_2(X1,X5,X6)))))))))))),
% 7.03/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.03/1.49  
% 7.03/1.49  fof(f12,plain,(
% 7.03/1.49    ! [X0] : (! [X1] : (! [X2] : ((v5_orders_3(X2,X0,X1) <=> ! [X3] : (! [X4] : ((! [X5] : (! [X6] : ((r1_orders_2(X1,X5,X6) | (k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5)) | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 7.03/1.49    inference(ennf_transformation,[],[f4])).
% 7.03/1.49  
% 7.03/1.49  fof(f13,plain,(
% 7.03/1.49    ! [X0] : (! [X1] : (! [X2] : ((v5_orders_3(X2,X0,X1) <=> ! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 7.03/1.49    inference(flattening,[],[f12])).
% 7.03/1.49  
% 7.03/1.49  fof(f20,plain,(
% 7.03/1.49    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 7.03/1.49    inference(definition_folding,[],[f13,f19,f18])).
% 7.03/1.49  
% 7.03/1.49  fof(f52,plain,(
% 7.03/1.49    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 7.03/1.49    inference(cnf_transformation,[],[f20])).
% 7.03/1.49  
% 7.03/1.49  fof(f62,plain,(
% 7.03/1.49    v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9))),
% 7.03/1.49    inference(cnf_transformation,[],[f36])).
% 7.03/1.49  
% 7.03/1.49  fof(f61,plain,(
% 7.03/1.49    v1_funct_1(sK11)),
% 7.03/1.49    inference(cnf_transformation,[],[f36])).
% 7.03/1.49  
% 7.03/1.49  fof(f56,plain,(
% 7.03/1.49    l1_orders_2(sK8)),
% 7.03/1.49    inference(cnf_transformation,[],[f36])).
% 7.03/1.49  
% 7.03/1.49  fof(f57,plain,(
% 7.03/1.49    l1_orders_2(sK9)),
% 7.03/1.49    inference(cnf_transformation,[],[f36])).
% 7.03/1.49  
% 7.03/1.49  fof(f63,plain,(
% 7.03/1.49    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))),
% 7.03/1.49    inference(cnf_transformation,[],[f36])).
% 7.03/1.49  
% 7.03/1.49  fof(f46,plain,(
% 7.03/1.49    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2))) )),
% 7.03/1.49    inference(cnf_transformation,[],[f29])).
% 7.03/1.49  
% 7.03/1.49  fof(f45,plain,(
% 7.03/1.49    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2))) )),
% 7.03/1.49    inference(cnf_transformation,[],[f29])).
% 7.03/1.49  
% 7.03/1.49  fof(f3,axiom,(
% 7.03/1.49    ! [X0] : (l1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)))),
% 7.03/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.03/1.49  
% 7.03/1.49  fof(f11,plain,(
% 7.03/1.49    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) | ~l1_orders_2(X0))),
% 7.03/1.49    inference(ennf_transformation,[],[f3])).
% 7.03/1.49  
% 7.03/1.49  fof(f40,plain,(
% 7.03/1.49    ( ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) | ~l1_orders_2(X0)) )),
% 7.03/1.49    inference(cnf_transformation,[],[f11])).
% 7.03/1.49  
% 7.03/1.49  fof(f64,plain,(
% 7.03/1.49    g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8))),
% 7.03/1.49    inference(cnf_transformation,[],[f36])).
% 7.03/1.49  
% 7.03/1.49  fof(f2,axiom,(
% 7.03/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 7.03/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.03/1.49  
% 7.03/1.49  fof(f10,plain,(
% 7.03/1.49    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 7.03/1.49    inference(ennf_transformation,[],[f2])).
% 7.03/1.49  
% 7.03/1.49  fof(f38,plain,(
% 7.03/1.49    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.03/1.49    inference(cnf_transformation,[],[f10])).
% 7.03/1.49  
% 7.03/1.49  fof(f54,plain,(
% 7.03/1.49    l1_orders_2(sK6)),
% 7.03/1.49    inference(cnf_transformation,[],[f36])).
% 7.03/1.49  
% 7.03/1.49  fof(f1,axiom,(
% 7.03/1.49    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 7.03/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.03/1.49  
% 7.03/1.49  fof(f9,plain,(
% 7.03/1.49    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.03/1.49    inference(ennf_transformation,[],[f1])).
% 7.03/1.49  
% 7.03/1.49  fof(f37,plain,(
% 7.03/1.49    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 7.03/1.49    inference(cnf_transformation,[],[f9])).
% 7.03/1.49  
% 7.03/1.49  fof(f5,axiom,(
% 7.03/1.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r1_orders_2(X0,X2,X3) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & X3 = X5 & X2 = X4) => r1_orders_2(X1,X4,X5))))))))),
% 7.03/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.03/1.49  
% 7.03/1.49  fof(f14,plain,(
% 7.03/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_orders_2(X1,X4,X5) | (~r1_orders_2(X0,X2,X3) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | X3 != X5 | X2 != X4)) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 7.03/1.49    inference(ennf_transformation,[],[f5])).
% 7.03/1.49  
% 7.03/1.49  fof(f15,plain,(
% 7.03/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_orders_2(X1,X4,X5) | ~r1_orders_2(X0,X2,X3) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | X3 != X5 | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 7.03/1.49    inference(flattening,[],[f14])).
% 7.03/1.49  
% 7.03/1.49  fof(f53,plain,(
% 7.03/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (r1_orders_2(X1,X4,X5) | ~r1_orders_2(X0,X2,X3) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | X3 != X5 | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 7.03/1.49    inference(cnf_transformation,[],[f15])).
% 7.03/1.49  
% 7.03/1.49  fof(f71,plain,(
% 7.03/1.49    ( ! [X4,X2,X0,X5,X1] : (r1_orders_2(X1,X4,X5) | ~r1_orders_2(X0,X2,X5) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 7.03/1.49    inference(equality_resolution,[],[f53])).
% 7.03/1.49  
% 7.03/1.49  fof(f72,plain,(
% 7.03/1.49    ( ! [X4,X0,X5,X1] : (r1_orders_2(X1,X4,X5) | ~r1_orders_2(X0,X4,X5) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 7.03/1.49    inference(equality_resolution,[],[f71])).
% 7.03/1.49  
% 7.03/1.49  fof(f44,plain,(
% 7.03/1.49    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2))) )),
% 7.03/1.49    inference(cnf_transformation,[],[f29])).
% 7.03/1.49  
% 7.03/1.49  fof(f43,plain,(
% 7.03/1.49    ( ! [X2,X0,X10,X8,X7,X1,X9] : (r1_orders_2(X0,X9,X10) | k1_funct_1(X1,X8) != X10 | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X0)) | ~m1_subset_1(X9,u1_struct_0(X0)) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 7.03/1.49    inference(cnf_transformation,[],[f29])).
% 7.03/1.49  
% 7.03/1.49  fof(f69,plain,(
% 7.03/1.49    ( ! [X2,X0,X8,X7,X1,X9] : (r1_orders_2(X0,X9,k1_funct_1(X1,X8)) | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0)) | ~m1_subset_1(X9,u1_struct_0(X0)) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 7.03/1.49    inference(equality_resolution,[],[f43])).
% 7.03/1.49  
% 7.03/1.49  fof(f70,plain,(
% 7.03/1.49    ( ! [X2,X0,X8,X7,X1] : (r1_orders_2(X0,k1_funct_1(X1,X7),k1_funct_1(X1,X8)) | ~m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0)) | ~m1_subset_1(k1_funct_1(X1,X7),u1_struct_0(X0)) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 7.03/1.49    inference(equality_resolution,[],[f69])).
% 7.03/1.49  
% 7.03/1.49  fof(f49,plain,(
% 7.03/1.49    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | k1_funct_1(X1,sK2(X0,X1,X2)) = sK4(X0,X1,X2)) )),
% 7.03/1.49    inference(cnf_transformation,[],[f29])).
% 7.03/1.49  
% 7.03/1.49  fof(f48,plain,(
% 7.03/1.49    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) )),
% 7.03/1.49    inference(cnf_transformation,[],[f29])).
% 7.03/1.49  
% 7.03/1.49  fof(f65,plain,(
% 7.03/1.49    g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9))),
% 7.03/1.49    inference(cnf_transformation,[],[f36])).
% 7.03/1.49  
% 7.03/1.49  fof(f55,plain,(
% 7.03/1.49    l1_orders_2(sK7)),
% 7.03/1.49    inference(cnf_transformation,[],[f36])).
% 7.03/1.49  
% 7.03/1.49  fof(f39,plain,(
% 7.03/1.49    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.03/1.49    inference(cnf_transformation,[],[f10])).
% 7.03/1.49  
% 7.03/1.49  fof(f41,plain,(
% 7.03/1.49    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | ~v5_orders_3(X1,X0,X2) | ~sP1(X0,X1,X2)) )),
% 7.03/1.49    inference(cnf_transformation,[],[f22])).
% 7.03/1.49  
% 7.03/1.49  fof(f67,plain,(
% 7.03/1.49    v5_orders_3(sK10,sK6,sK7)),
% 7.03/1.49    inference(cnf_transformation,[],[f36])).
% 7.03/1.49  
% 7.03/1.49  fof(f66,plain,(
% 7.03/1.49    sK10 = sK11),
% 7.03/1.49    inference(cnf_transformation,[],[f36])).
% 7.03/1.49  
% 7.03/1.49  fof(f59,plain,(
% 7.03/1.49    v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7))),
% 7.03/1.49    inference(cnf_transformation,[],[f36])).
% 7.03/1.49  
% 7.03/1.49  fof(f58,plain,(
% 7.03/1.49    v1_funct_1(sK10)),
% 7.03/1.49    inference(cnf_transformation,[],[f36])).
% 7.03/1.49  
% 7.03/1.49  fof(f60,plain,(
% 7.03/1.49    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))),
% 7.03/1.49    inference(cnf_transformation,[],[f36])).
% 7.03/1.49  
% 7.03/1.49  fof(f51,plain,(
% 7.03/1.49    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2))) )),
% 7.03/1.49    inference(cnf_transformation,[],[f29])).
% 7.03/1.49  
% 7.03/1.49  fof(f47,plain,(
% 7.03/1.49    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) )),
% 7.03/1.49    inference(cnf_transformation,[],[f29])).
% 7.03/1.49  
% 7.03/1.49  cnf(c_7,plain,
% 7.03/1.49      ( sP0(X0,X1,X2) | k1_funct_1(X1,sK3(X0,X1,X2)) = sK5(X0,X1,X2) ),
% 7.03/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_2456,plain,
% 7.03/1.49      ( k1_funct_1(X0,sK3(X1,X0,X2)) = sK5(X1,X0,X2)
% 7.03/1.49      | sP0(X1,X0,X2) = iProver_top ),
% 7.03/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_4,plain,
% 7.03/1.49      ( ~ sP1(X0,X1,X2) | ~ sP0(X2,X1,X0) | v5_orders_3(X1,X0,X2) ),
% 7.03/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_17,negated_conjecture,
% 7.03/1.49      ( ~ v5_orders_3(sK11,sK8,sK9) ),
% 7.03/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_321,plain,
% 7.03/1.49      ( ~ sP1(X0,X1,X2)
% 7.03/1.49      | ~ sP0(X2,X1,X0)
% 7.03/1.49      | sK9 != X2
% 7.03/1.49      | sK8 != X0
% 7.03/1.49      | sK11 != X1 ),
% 7.03/1.49      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_322,plain,
% 7.03/1.49      ( ~ sP1(sK8,sK11,sK9) | ~ sP0(sK9,sK11,sK8) ),
% 7.03/1.49      inference(unflattening,[status(thm)],[c_321]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_15,plain,
% 7.03/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.03/1.49      | sP1(X1,X0,X2)
% 7.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.03/1.49      | ~ v1_funct_1(X0)
% 7.03/1.49      | ~ l1_orders_2(X1)
% 7.03/1.49      | ~ l1_orders_2(X2) ),
% 7.03/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_23,negated_conjecture,
% 7.03/1.49      ( v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) ),
% 7.03/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_358,plain,
% 7.03/1.49      ( sP1(X0,X1,X2)
% 7.03/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
% 7.03/1.49      | ~ v1_funct_1(X1)
% 7.03/1.49      | ~ l1_orders_2(X0)
% 7.03/1.49      | ~ l1_orders_2(X2)
% 7.03/1.49      | u1_struct_0(X2) != u1_struct_0(sK9)
% 7.03/1.49      | u1_struct_0(X0) != u1_struct_0(sK8)
% 7.03/1.49      | sK11 != X1 ),
% 7.03/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_359,plain,
% 7.03/1.49      ( sP1(X0,sK11,X1)
% 7.03/1.49      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.03/1.49      | ~ v1_funct_1(sK11)
% 7.03/1.49      | ~ l1_orders_2(X0)
% 7.03/1.49      | ~ l1_orders_2(X1)
% 7.03/1.49      | u1_struct_0(X1) != u1_struct_0(sK9)
% 7.03/1.49      | u1_struct_0(X0) != u1_struct_0(sK8) ),
% 7.03/1.49      inference(unflattening,[status(thm)],[c_358]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_24,negated_conjecture,
% 7.03/1.49      ( v1_funct_1(sK11) ),
% 7.03/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_363,plain,
% 7.03/1.49      ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.03/1.49      | sP1(X0,sK11,X1)
% 7.03/1.49      | ~ l1_orders_2(X0)
% 7.03/1.49      | ~ l1_orders_2(X1)
% 7.03/1.49      | u1_struct_0(X1) != u1_struct_0(sK9)
% 7.03/1.49      | u1_struct_0(X0) != u1_struct_0(sK8) ),
% 7.03/1.49      inference(global_propositional_subsumption,
% 7.03/1.49                [status(thm)],
% 7.03/1.49                [c_359,c_24]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_364,plain,
% 7.03/1.49      ( sP1(X0,sK11,X1)
% 7.03/1.49      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.03/1.49      | ~ l1_orders_2(X0)
% 7.03/1.49      | ~ l1_orders_2(X1)
% 7.03/1.49      | u1_struct_0(X1) != u1_struct_0(sK9)
% 7.03/1.49      | u1_struct_0(X0) != u1_struct_0(sK8) ),
% 7.03/1.49      inference(renaming,[status(thm)],[c_363]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_432,plain,
% 7.03/1.49      ( ~ sP0(sK9,sK11,sK8)
% 7.03/1.49      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.03/1.49      | ~ l1_orders_2(X0)
% 7.03/1.49      | ~ l1_orders_2(X1)
% 7.03/1.49      | u1_struct_0(X1) != u1_struct_0(sK9)
% 7.03/1.49      | u1_struct_0(X0) != u1_struct_0(sK8)
% 7.03/1.49      | sK9 != X1
% 7.03/1.49      | sK8 != X0
% 7.03/1.49      | sK11 != sK11 ),
% 7.03/1.49      inference(resolution_lifted,[status(thm)],[c_322,c_364]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_433,plain,
% 7.03/1.49      ( ~ sP0(sK9,sK11,sK8)
% 7.03/1.49      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
% 7.03/1.49      | ~ l1_orders_2(sK9)
% 7.03/1.49      | ~ l1_orders_2(sK8)
% 7.03/1.49      | u1_struct_0(sK9) != u1_struct_0(sK9)
% 7.03/1.49      | u1_struct_0(sK8) != u1_struct_0(sK8) ),
% 7.03/1.49      inference(unflattening,[status(thm)],[c_432]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_29,negated_conjecture,
% 7.03/1.49      ( l1_orders_2(sK8) ),
% 7.03/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_28,negated_conjecture,
% 7.03/1.49      ( l1_orders_2(sK9) ),
% 7.03/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_22,negated_conjecture,
% 7.03/1.49      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) ),
% 7.03/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_435,plain,
% 7.03/1.49      ( ~ sP0(sK9,sK11,sK8)
% 7.03/1.49      | u1_struct_0(sK9) != u1_struct_0(sK9)
% 7.03/1.49      | u1_struct_0(sK8) != u1_struct_0(sK8) ),
% 7.03/1.49      inference(global_propositional_subsumption,
% 7.03/1.49                [status(thm)],
% 7.03/1.49                [c_433,c_29,c_28,c_22]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_1052,plain,
% 7.03/1.49      ( ~ sP0(sK9,sK11,sK8) ),
% 7.03/1.49      inference(equality_resolution_simp,[status(thm)],[c_435]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_2440,plain,
% 7.03/1.49      ( sP0(sK9,sK11,sK8) != iProver_top ),
% 7.03/1.49      inference(predicate_to_equality,[status(thm)],[c_1052]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_4462,plain,
% 7.03/1.49      ( k1_funct_1(sK11,sK3(sK9,sK11,sK8)) = sK5(sK9,sK11,sK8) ),
% 7.03/1.49      inference(superposition,[status(thm)],[c_2456,c_2440]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_11,plain,
% 7.03/1.49      ( r1_orders_2(X0,sK2(X1,X2,X0),sK3(X1,X2,X0)) | sP0(X1,X2,X0) ),
% 7.03/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2452,plain,
% 7.03/1.50      ( r1_orders_2(X0,sK2(X1,X2,X0),sK3(X1,X2,X0)) = iProver_top
% 7.03/1.50      | sP0(X1,X2,X0) = iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_12,plain,
% 7.03/1.50      ( sP0(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2)) ),
% 7.03/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2451,plain,
% 7.03/1.50      ( sP0(X0,X1,X2) = iProver_top
% 7.03/1.50      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2)) = iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2444,plain,
% 7.03/1.50      ( l1_orders_2(sK8) = iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_3,plain,
% 7.03/1.50      ( ~ l1_orders_2(X0)
% 7.03/1.50      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ),
% 7.03/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2458,plain,
% 7.03/1.50      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0))
% 7.03/1.50      | l1_orders_2(X0) != iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2937,plain,
% 7.03/1.50      ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) = k7_lattice3(k7_lattice3(sK8)) ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_2444,c_2458]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_21,negated_conjecture,
% 7.03/1.50      ( g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) ),
% 7.03/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_3117,plain,
% 7.03/1.50      ( g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = k7_lattice3(k7_lattice3(sK8)) ),
% 7.03/1.50      inference(demodulation,[status(thm)],[c_2937,c_21]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2,plain,
% 7.03/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.03/1.50      | X2 = X1
% 7.03/1.50      | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
% 7.03/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2459,plain,
% 7.03/1.50      ( X0 = X1
% 7.03/1.50      | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
% 7.03/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_4756,plain,
% 7.03/1.50      ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK8))
% 7.03/1.50      | u1_struct_0(sK6) = X0
% 7.03/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_3117,c_2459]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_31,negated_conjecture,
% 7.03/1.50      ( l1_orders_2(sK6) ),
% 7.03/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_32,plain,
% 7.03/1.50      ( l1_orders_2(sK6) = iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_0,plain,
% 7.03/1.50      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 7.03/1.50      | ~ l1_orders_2(X0) ),
% 7.03/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_88,plain,
% 7.03/1.50      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
% 7.03/1.50      | l1_orders_2(X0) != iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_90,plain,
% 7.03/1.50      ( m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) = iProver_top
% 7.03/1.50      | l1_orders_2(sK6) != iProver_top ),
% 7.03/1.50      inference(instantiation,[status(thm)],[c_88]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_4760,plain,
% 7.03/1.50      ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK8))
% 7.03/1.50      | u1_struct_0(sK6) = X0
% 7.03/1.50      | m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_3117,c_2459]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_4893,plain,
% 7.03/1.50      ( u1_struct_0(sK6) = X0
% 7.03/1.50      | g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK8)) ),
% 7.03/1.50      inference(global_propositional_subsumption,
% 7.03/1.50                [status(thm)],
% 7.03/1.50                [c_4756,c_32,c_90,c_4760]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_4894,plain,
% 7.03/1.50      ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK8))
% 7.03/1.50      | u1_struct_0(sK6) = X0 ),
% 7.03/1.50      inference(renaming,[status(thm)],[c_4893]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_4901,plain,
% 7.03/1.50      ( u1_struct_0(sK8) = u1_struct_0(sK6) ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_2937,c_4894]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_16,plain,
% 7.03/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 7.03/1.50      | r1_orders_2(X3,X1,X2)
% 7.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 7.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X3))
% 7.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.03/1.50      | ~ l1_orders_2(X0)
% 7.03/1.50      | ~ l1_orders_2(X3)
% 7.03/1.50      | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
% 7.03/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2448,plain,
% 7.03/1.50      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
% 7.03/1.50      | r1_orders_2(X1,X2,X3) != iProver_top
% 7.03/1.50      | r1_orders_2(X0,X2,X3) = iProver_top
% 7.03/1.50      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 7.03/1.50      | l1_orders_2(X1) != iProver_top
% 7.03/1.50      | l1_orders_2(X0) != iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_3374,plain,
% 7.03/1.50      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK8))
% 7.03/1.50      | r1_orders_2(X0,X1,X2) != iProver_top
% 7.03/1.50      | r1_orders_2(sK6,X1,X2) = iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
% 7.03/1.50      | l1_orders_2(X0) != iProver_top
% 7.03/1.50      | l1_orders_2(sK6) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_3117,c_2448]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_3836,plain,
% 7.03/1.50      ( l1_orders_2(X0) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | r1_orders_2(sK6,X1,X2) = iProver_top
% 7.03/1.50      | r1_orders_2(X0,X1,X2) != iProver_top
% 7.03/1.50      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK8)) ),
% 7.03/1.50      inference(global_propositional_subsumption,
% 7.03/1.50                [status(thm)],
% 7.03/1.50                [c_3374,c_32]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_3837,plain,
% 7.03/1.50      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK8))
% 7.03/1.50      | r1_orders_2(X0,X1,X2) != iProver_top
% 7.03/1.50      | r1_orders_2(sK6,X1,X2) = iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
% 7.03/1.50      | l1_orders_2(X0) != iProver_top ),
% 7.03/1.50      inference(renaming,[status(thm)],[c_3836]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_3851,plain,
% 7.03/1.50      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 7.03/1.50      | r1_orders_2(sK8,X0,X1) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 7.03/1.50      | l1_orders_2(sK8) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_2937,c_3837]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_34,plain,
% 7.03/1.50      ( l1_orders_2(sK8) = iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_4314,plain,
% 7.03/1.50      ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 7.03/1.50      | r1_orders_2(sK8,X0,X1) != iProver_top
% 7.03/1.50      | r1_orders_2(sK6,X0,X1) = iProver_top ),
% 7.03/1.50      inference(global_propositional_subsumption,
% 7.03/1.50                [status(thm)],
% 7.03/1.50                [c_3851,c_34]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_4315,plain,
% 7.03/1.50      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 7.03/1.50      | r1_orders_2(sK8,X0,X1) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 7.03/1.50      inference(renaming,[status(thm)],[c_4314]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_5013,plain,
% 7.03/1.50      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 7.03/1.50      | r1_orders_2(sK8,X0,X1) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 7.03/1.50      inference(demodulation,[status(thm)],[c_4901,c_4315]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_9070,plain,
% 7.03/1.50      ( r1_orders_2(sK6,X0,sK3(X1,X2,sK8)) = iProver_top
% 7.03/1.50      | r1_orders_2(sK8,X0,sK3(X1,X2,sK8)) != iProver_top
% 7.03/1.50      | sP0(X1,X2,sK8) = iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_2451,c_5013]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_9536,plain,
% 7.03/1.50      ( r1_orders_2(sK6,sK2(X0,X1,sK8),sK3(X0,X1,sK8)) = iProver_top
% 7.03/1.50      | sP0(X0,X1,sK8) = iProver_top
% 7.03/1.50      | m1_subset_1(sK2(X0,X1,sK8),u1_struct_0(sK8)) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_2452,c_9070]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_13,plain,
% 7.03/1.50      ( sP0(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) ),
% 7.03/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_3924,plain,
% 7.03/1.50      ( sP0(X0,X1,sK8) | m1_subset_1(sK2(X0,X1,sK8),u1_struct_0(sK8)) ),
% 7.03/1.50      inference(instantiation,[status(thm)],[c_13]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_3940,plain,
% 7.03/1.50      ( sP0(X0,X1,sK8) = iProver_top
% 7.03/1.50      | m1_subset_1(sK2(X0,X1,sK8),u1_struct_0(sK8)) = iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_3924]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_9541,plain,
% 7.03/1.50      ( sP0(X0,X1,sK8) = iProver_top
% 7.03/1.50      | r1_orders_2(sK6,sK2(X0,X1,sK8),sK3(X0,X1,sK8)) = iProver_top ),
% 7.03/1.50      inference(global_propositional_subsumption,
% 7.03/1.50                [status(thm)],
% 7.03/1.50                [c_9536,c_3940]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_9542,plain,
% 7.03/1.50      ( r1_orders_2(sK6,sK2(X0,X1,sK8),sK3(X0,X1,sK8)) = iProver_top
% 7.03/1.50      | sP0(X0,X1,sK8) = iProver_top ),
% 7.03/1.50      inference(renaming,[status(thm)],[c_9541]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_14,plain,
% 7.03/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 7.03/1.50      | r1_orders_2(X3,k1_funct_1(X4,X1),k1_funct_1(X4,X2))
% 7.03/1.50      | ~ sP0(X3,X4,X0)
% 7.03/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.03/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.03/1.50      | ~ m1_subset_1(k1_funct_1(X4,X2),u1_struct_0(X3))
% 7.03/1.50      | ~ m1_subset_1(k1_funct_1(X4,X1),u1_struct_0(X3)) ),
% 7.03/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2449,plain,
% 7.03/1.50      ( r1_orders_2(X0,X1,X2) != iProver_top
% 7.03/1.50      | r1_orders_2(X3,k1_funct_1(X4,X1),k1_funct_1(X4,X2)) = iProver_top
% 7.03/1.50      | sP0(X3,X4,X0) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(k1_funct_1(X4,X2),u1_struct_0(X3)) != iProver_top
% 7.03/1.50      | m1_subset_1(k1_funct_1(X4,X1),u1_struct_0(X3)) != iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_9549,plain,
% 7.03/1.50      ( r1_orders_2(X0,k1_funct_1(X1,sK2(X2,X3,sK8)),k1_funct_1(X1,sK3(X2,X3,sK8))) = iProver_top
% 7.03/1.50      | sP0(X0,X1,sK6) != iProver_top
% 7.03/1.50      | sP0(X2,X3,sK8) = iProver_top
% 7.03/1.50      | m1_subset_1(sK2(X2,X3,sK8),u1_struct_0(sK6)) != iProver_top
% 7.03/1.50      | m1_subset_1(sK3(X2,X3,sK8),u1_struct_0(sK6)) != iProver_top
% 7.03/1.50      | m1_subset_1(k1_funct_1(X1,sK2(X2,X3,sK8)),u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(k1_funct_1(X1,sK3(X2,X3,sK8)),u1_struct_0(X0)) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_9542,c_2449]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_9562,plain,
% 7.03/1.50      ( r1_orders_2(X0,k1_funct_1(X1,sK2(X2,X3,sK8)),k1_funct_1(X1,sK3(X2,X3,sK8))) = iProver_top
% 7.03/1.50      | sP0(X0,X1,sK6) != iProver_top
% 7.03/1.50      | sP0(X2,X3,sK8) = iProver_top
% 7.03/1.50      | m1_subset_1(sK2(X2,X3,sK8),u1_struct_0(sK8)) != iProver_top
% 7.03/1.50      | m1_subset_1(sK3(X2,X3,sK8),u1_struct_0(sK8)) != iProver_top
% 7.03/1.50      | m1_subset_1(k1_funct_1(X1,sK2(X2,X3,sK8)),u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(k1_funct_1(X1,sK3(X2,X3,sK8)),u1_struct_0(X0)) != iProver_top ),
% 7.03/1.50      inference(light_normalisation,[status(thm)],[c_9549,c_4901]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2450,plain,
% 7.03/1.50      ( sP0(X0,X1,X2) = iProver_top
% 7.03/1.50      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) = iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_9834,plain,
% 7.03/1.50      ( r1_orders_2(X0,k1_funct_1(X1,sK2(X2,X3,sK8)),k1_funct_1(X1,sK3(X2,X3,sK8))) = iProver_top
% 7.03/1.50      | sP0(X0,X1,sK6) != iProver_top
% 7.03/1.50      | sP0(X2,X3,sK8) = iProver_top
% 7.03/1.50      | m1_subset_1(k1_funct_1(X1,sK2(X2,X3,sK8)),u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(k1_funct_1(X1,sK3(X2,X3,sK8)),u1_struct_0(X0)) != iProver_top ),
% 7.03/1.50      inference(forward_subsumption_resolution,
% 7.03/1.50                [status(thm)],
% 7.03/1.50                [c_9562,c_2451,c_2450]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_9839,plain,
% 7.03/1.50      ( r1_orders_2(X0,k1_funct_1(sK11,sK2(sK9,sK11,sK8)),sK5(sK9,sK11,sK8)) = iProver_top
% 7.03/1.50      | sP0(X0,sK11,sK6) != iProver_top
% 7.03/1.50      | sP0(sK9,sK11,sK8) = iProver_top
% 7.03/1.50      | m1_subset_1(k1_funct_1(sK11,sK2(sK9,sK11,sK8)),u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(k1_funct_1(sK11,sK3(sK9,sK11,sK8)),u1_struct_0(X0)) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_4462,c_9834]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_8,plain,
% 7.03/1.50      ( sP0(X0,X1,X2) | k1_funct_1(X1,sK2(X0,X1,X2)) = sK4(X0,X1,X2) ),
% 7.03/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2455,plain,
% 7.03/1.50      ( k1_funct_1(X0,sK2(X1,X0,X2)) = sK4(X1,X0,X2)
% 7.03/1.50      | sP0(X1,X0,X2) = iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_3680,plain,
% 7.03/1.50      ( k1_funct_1(sK11,sK2(sK9,sK11,sK8)) = sK4(sK9,sK11,sK8) ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_2455,c_2440]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_9876,plain,
% 7.03/1.50      ( r1_orders_2(X0,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
% 7.03/1.50      | sP0(X0,sK11,sK6) != iProver_top
% 7.03/1.50      | sP0(sK9,sK11,sK8) = iProver_top
% 7.03/1.50      | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(X0)) != iProver_top ),
% 7.03/1.50      inference(light_normalisation,[status(thm)],[c_9839,c_3680,c_4462]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_1053,plain,
% 7.03/1.50      ( sP0(sK9,sK11,sK8) != iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_1052]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_24141,plain,
% 7.03/1.50      ( sP0(X0,sK11,sK6) != iProver_top
% 7.03/1.50      | r1_orders_2(X0,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
% 7.03/1.50      | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(X0)) != iProver_top ),
% 7.03/1.50      inference(global_propositional_subsumption,
% 7.03/1.50                [status(thm)],
% 7.03/1.50                [c_9876,c_1053]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_24142,plain,
% 7.03/1.50      ( r1_orders_2(X0,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
% 7.03/1.50      | sP0(X0,sK11,sK6) != iProver_top
% 7.03/1.50      | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(X0)) != iProver_top ),
% 7.03/1.50      inference(renaming,[status(thm)],[c_24141]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_9,plain,
% 7.03/1.50      ( sP0(X0,X1,X2) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ),
% 7.03/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2454,plain,
% 7.03/1.50      ( sP0(X0,X1,X2) = iProver_top
% 7.03/1.50      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) = iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2445,plain,
% 7.03/1.50      ( l1_orders_2(sK9) = iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2936,plain,
% 7.03/1.50      ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) = k7_lattice3(k7_lattice3(sK9)) ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_2445,c_2458]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_20,negated_conjecture,
% 7.03/1.50      ( g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
% 7.03/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2987,plain,
% 7.03/1.50      ( g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = k7_lattice3(k7_lattice3(sK9)) ),
% 7.03/1.50      inference(demodulation,[status(thm)],[c_2936,c_20]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_3376,plain,
% 7.03/1.50      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK9))
% 7.03/1.50      | r1_orders_2(X0,X1,X2) = iProver_top
% 7.03/1.50      | r1_orders_2(sK7,X1,X2) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | l1_orders_2(X0) != iProver_top
% 7.03/1.50      | l1_orders_2(sK7) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_2987,c_2448]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_30,negated_conjecture,
% 7.03/1.50      ( l1_orders_2(sK7) ),
% 7.03/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_33,plain,
% 7.03/1.50      ( l1_orders_2(sK7) = iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_4037,plain,
% 7.03/1.50      ( l1_orders_2(X0) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | r1_orders_2(sK7,X1,X2) != iProver_top
% 7.03/1.50      | r1_orders_2(X0,X1,X2) = iProver_top
% 7.03/1.50      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK9)) ),
% 7.03/1.50      inference(global_propositional_subsumption,
% 7.03/1.50                [status(thm)],
% 7.03/1.50                [c_3376,c_33]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_4038,plain,
% 7.03/1.50      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK9))
% 7.03/1.50      | r1_orders_2(X0,X1,X2) = iProver_top
% 7.03/1.50      | r1_orders_2(sK7,X1,X2) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | l1_orders_2(X0) != iProver_top ),
% 7.03/1.50      inference(renaming,[status(thm)],[c_4037]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_4052,plain,
% 7.03/1.50      ( r1_orders_2(sK7,X0,X1) != iProver_top
% 7.03/1.50      | r1_orders_2(sK9,X0,X1) = iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | l1_orders_2(sK9) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_2936,c_4038]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_1,plain,
% 7.03/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.03/1.50      | X2 = X0
% 7.03/1.50      | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
% 7.03/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2460,plain,
% 7.03/1.50      ( X0 = X1
% 7.03/1.50      | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
% 7.03/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_5341,plain,
% 7.03/1.50      ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK9))
% 7.03/1.50      | u1_orders_2(sK7) = X1
% 7.03/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_2987,c_2460]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_5345,plain,
% 7.03/1.50      ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK9))
% 7.03/1.50      | u1_orders_2(sK7) = X1
% 7.03/1.50      | m1_subset_1(u1_orders_2(sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7)))) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_2987,c_2460]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_5410,plain,
% 7.03/1.50      ( ~ m1_subset_1(u1_orders_2(sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7))))
% 7.03/1.50      | g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK9))
% 7.03/1.50      | u1_orders_2(sK7) = X1 ),
% 7.03/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_5345]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_5473,plain,
% 7.03/1.50      ( m1_subset_1(u1_orders_2(sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7))))
% 7.03/1.50      | ~ l1_orders_2(sK7) ),
% 7.03/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_5623,plain,
% 7.03/1.50      ( u1_orders_2(sK7) = X1
% 7.03/1.50      | g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK9)) ),
% 7.03/1.50      inference(global_propositional_subsumption,
% 7.03/1.50                [status(thm)],
% 7.03/1.50                [c_5341,c_30,c_5410,c_5473]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_5624,plain,
% 7.03/1.50      ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK9))
% 7.03/1.50      | u1_orders_2(sK7) = X1 ),
% 7.03/1.50      inference(renaming,[status(thm)],[c_5623]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_5629,plain,
% 7.03/1.50      ( u1_orders_2(sK9) = u1_orders_2(sK7) ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_2936,c_5624]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_3373,plain,
% 7.03/1.50      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK9))
% 7.03/1.50      | r1_orders_2(X0,X1,X2) != iProver_top
% 7.03/1.50      | r1_orders_2(sK9,X1,X2) = iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | l1_orders_2(X0) != iProver_top
% 7.03/1.50      | l1_orders_2(sK9) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_2936,c_2448]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_35,plain,
% 7.03/1.50      ( l1_orders_2(sK9) = iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_5931,plain,
% 7.03/1.50      ( l1_orders_2(X0) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | r1_orders_2(sK9,X1,X2) = iProver_top
% 7.03/1.50      | r1_orders_2(X0,X1,X2) != iProver_top
% 7.03/1.50      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK9)) ),
% 7.03/1.50      inference(global_propositional_subsumption,
% 7.03/1.50                [status(thm)],
% 7.03/1.50                [c_3373,c_35]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_5932,plain,
% 7.03/1.50      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK9))
% 7.03/1.50      | r1_orders_2(X0,X1,X2) != iProver_top
% 7.03/1.50      | r1_orders_2(sK9,X1,X2) = iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.03/1.50      | m1_subset_1(X2,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | l1_orders_2(X0) != iProver_top ),
% 7.03/1.50      inference(renaming,[status(thm)],[c_5931]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_5948,plain,
% 7.03/1.50      ( g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK9)) != k7_lattice3(k7_lattice3(sK9))
% 7.03/1.50      | r1_orders_2(sK7,X0,X1) != iProver_top
% 7.03/1.50      | r1_orders_2(sK9,X0,X1) = iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | l1_orders_2(sK7) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_5629,c_5932]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_5654,plain,
% 7.03/1.50      ( g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK9)) = k7_lattice3(k7_lattice3(sK9)) ),
% 7.03/1.50      inference(demodulation,[status(thm)],[c_5629,c_2987]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_5957,plain,
% 7.03/1.50      ( k7_lattice3(k7_lattice3(sK9)) != k7_lattice3(k7_lattice3(sK9))
% 7.03/1.50      | r1_orders_2(sK7,X0,X1) != iProver_top
% 7.03/1.50      | r1_orders_2(sK9,X0,X1) = iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | l1_orders_2(sK7) != iProver_top ),
% 7.03/1.50      inference(light_normalisation,[status(thm)],[c_5948,c_5654]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_5958,plain,
% 7.03/1.50      ( r1_orders_2(sK7,X0,X1) != iProver_top
% 7.03/1.50      | r1_orders_2(sK9,X0,X1) = iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | l1_orders_2(sK7) != iProver_top ),
% 7.03/1.50      inference(equality_resolution_simp,[status(thm)],[c_5957]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_7284,plain,
% 7.03/1.50      ( m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | r1_orders_2(sK9,X0,X1) = iProver_top
% 7.03/1.50      | r1_orders_2(sK7,X0,X1) != iProver_top ),
% 7.03/1.50      inference(global_propositional_subsumption,
% 7.03/1.50                [status(thm)],
% 7.03/1.50                [c_4052,c_33,c_5958]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_7285,plain,
% 7.03/1.50      ( r1_orders_2(sK7,X0,X1) != iProver_top
% 7.03/1.50      | r1_orders_2(sK9,X0,X1) = iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 7.03/1.50      inference(renaming,[status(thm)],[c_7284]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_4754,plain,
% 7.03/1.50      ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK9))
% 7.03/1.50      | u1_struct_0(sK7) = X0
% 7.03/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_2987,c_2459]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_4840,plain,
% 7.03/1.50      ( u1_struct_0(sK9) = u1_struct_0(sK7)
% 7.03/1.50      | m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)))) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_2936,c_4754]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_4221,plain,
% 7.03/1.50      ( m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
% 7.03/1.50      | ~ l1_orders_2(sK9) ),
% 7.03/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_4226,plain,
% 7.03/1.50      ( m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)))) = iProver_top
% 7.03/1.50      | l1_orders_2(sK9) != iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_4221]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_6161,plain,
% 7.03/1.50      ( u1_struct_0(sK9) = u1_struct_0(sK7) ),
% 7.03/1.50      inference(global_propositional_subsumption,
% 7.03/1.50                [status(thm)],
% 7.03/1.50                [c_4840,c_35,c_4226]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_7290,plain,
% 7.03/1.50      ( r1_orders_2(sK7,X0,X1) != iProver_top
% 7.03/1.50      | r1_orders_2(sK9,X0,X1) = iProver_top
% 7.03/1.50      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 7.03/1.50      inference(light_normalisation,[status(thm)],[c_7285,c_6161]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_7298,plain,
% 7.03/1.50      ( r1_orders_2(sK7,X0,sK5(sK9,X1,X2)) != iProver_top
% 7.03/1.50      | r1_orders_2(sK9,X0,sK5(sK9,X1,X2)) = iProver_top
% 7.03/1.50      | sP0(sK9,X1,X2) = iProver_top
% 7.03/1.50      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_2454,c_7290]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_24154,plain,
% 7.03/1.50      ( r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
% 7.03/1.50      | sP0(sK7,sK11,sK6) != iProver_top
% 7.03/1.50      | sP0(sK9,sK11,sK8) = iProver_top
% 7.03/1.50      | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK7)) != iProver_top
% 7.03/1.50      | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top ),
% 7.03/1.50      inference(superposition,[status(thm)],[c_24142,c_7298]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_24172,plain,
% 7.03/1.50      ( r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
% 7.03/1.50      | sP0(sK7,sK11,sK6) != iProver_top
% 7.03/1.50      | sP0(sK9,sK11,sK8) = iProver_top
% 7.03/1.50      | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top
% 7.03/1.50      | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top ),
% 7.03/1.50      inference(light_normalisation,[status(thm)],[c_24154,c_6161]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_5,plain,
% 7.03/1.50      ( ~ sP1(X0,X1,X2) | sP0(X2,X1,X0) | ~ v5_orders_3(X1,X0,X2) ),
% 7.03/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_18,negated_conjecture,
% 7.03/1.50      ( v5_orders_3(sK10,sK6,sK7) ),
% 7.03/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_331,plain,
% 7.03/1.50      ( ~ sP1(X0,X1,X2)
% 7.03/1.50      | sP0(X2,X1,X0)
% 7.03/1.50      | sK7 != X2
% 7.03/1.50      | sK6 != X0
% 7.03/1.50      | sK10 != X1 ),
% 7.03/1.50      inference(resolution_lifted,[status(thm)],[c_5,c_18]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_332,plain,
% 7.03/1.50      ( ~ sP1(sK6,sK10,sK7) | sP0(sK7,sK10,sK6) ),
% 7.03/1.50      inference(unflattening,[status(thm)],[c_331]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_469,plain,
% 7.03/1.50      ( sP0(sK7,sK10,sK6)
% 7.03/1.50      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.03/1.50      | ~ l1_orders_2(X0)
% 7.03/1.50      | ~ l1_orders_2(X1)
% 7.03/1.50      | u1_struct_0(X1) != u1_struct_0(sK9)
% 7.03/1.50      | u1_struct_0(X0) != u1_struct_0(sK8)
% 7.03/1.50      | sK7 != X1
% 7.03/1.50      | sK6 != X0
% 7.03/1.50      | sK10 != sK11 ),
% 7.03/1.50      inference(resolution_lifted,[status(thm)],[c_332,c_364]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_470,plain,
% 7.03/1.50      ( sP0(sK7,sK10,sK6)
% 7.03/1.50      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 7.03/1.50      | ~ l1_orders_2(sK7)
% 7.03/1.50      | ~ l1_orders_2(sK6)
% 7.03/1.50      | u1_struct_0(sK7) != u1_struct_0(sK9)
% 7.03/1.50      | u1_struct_0(sK6) != u1_struct_0(sK8)
% 7.03/1.50      | sK10 != sK11 ),
% 7.03/1.50      inference(unflattening,[status(thm)],[c_469]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_19,negated_conjecture,
% 7.03/1.50      ( sK10 = sK11 ),
% 7.03/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_472,plain,
% 7.03/1.50      ( u1_struct_0(sK6) != u1_struct_0(sK8)
% 7.03/1.50      | u1_struct_0(sK7) != u1_struct_0(sK9)
% 7.03/1.50      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 7.03/1.50      | sP0(sK7,sK10,sK6) ),
% 7.03/1.50      inference(global_propositional_subsumption,
% 7.03/1.50                [status(thm)],
% 7.03/1.50                [c_470,c_31,c_30,c_19]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_473,plain,
% 7.03/1.50      ( sP0(sK7,sK10,sK6)
% 7.03/1.50      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 7.03/1.50      | u1_struct_0(sK7) != u1_struct_0(sK9)
% 7.03/1.50      | u1_struct_0(sK6) != u1_struct_0(sK8) ),
% 7.03/1.50      inference(renaming,[status(thm)],[c_472]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_26,negated_conjecture,
% 7.03/1.50      ( v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7)) ),
% 7.03/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_388,plain,
% 7.03/1.50      ( sP1(X0,X1,X2)
% 7.03/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
% 7.03/1.50      | ~ v1_funct_1(X1)
% 7.03/1.50      | ~ l1_orders_2(X0)
% 7.03/1.50      | ~ l1_orders_2(X2)
% 7.03/1.50      | u1_struct_0(X2) != u1_struct_0(sK7)
% 7.03/1.50      | u1_struct_0(X0) != u1_struct_0(sK6)
% 7.03/1.50      | sK10 != X1 ),
% 7.03/1.50      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_389,plain,
% 7.03/1.50      ( sP1(X0,sK10,X1)
% 7.03/1.50      | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.03/1.50      | ~ v1_funct_1(sK10)
% 7.03/1.50      | ~ l1_orders_2(X0)
% 7.03/1.50      | ~ l1_orders_2(X1)
% 7.03/1.50      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.03/1.50      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 7.03/1.50      inference(unflattening,[status(thm)],[c_388]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_27,negated_conjecture,
% 7.03/1.50      ( v1_funct_1(sK10) ),
% 7.03/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_393,plain,
% 7.03/1.50      ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.03/1.50      | sP1(X0,sK10,X1)
% 7.03/1.50      | ~ l1_orders_2(X0)
% 7.03/1.50      | ~ l1_orders_2(X1)
% 7.03/1.50      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.03/1.50      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 7.03/1.50      inference(global_propositional_subsumption,
% 7.03/1.50                [status(thm)],
% 7.03/1.50                [c_389,c_27]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_394,plain,
% 7.03/1.50      ( sP1(X0,sK10,X1)
% 7.03/1.50      | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.03/1.50      | ~ l1_orders_2(X0)
% 7.03/1.50      | ~ l1_orders_2(X1)
% 7.03/1.50      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.03/1.50      | u1_struct_0(X0) != u1_struct_0(sK6) ),
% 7.03/1.50      inference(renaming,[status(thm)],[c_393]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_489,plain,
% 7.03/1.50      ( sP0(sK7,sK10,sK6)
% 7.03/1.50      | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.03/1.50      | ~ l1_orders_2(X0)
% 7.03/1.50      | ~ l1_orders_2(X1)
% 7.03/1.50      | u1_struct_0(X1) != u1_struct_0(sK7)
% 7.03/1.50      | u1_struct_0(X0) != u1_struct_0(sK6)
% 7.03/1.50      | sK7 != X1
% 7.03/1.50      | sK6 != X0
% 7.03/1.50      | sK10 != sK10 ),
% 7.03/1.50      inference(resolution_lifted,[status(thm)],[c_332,c_394]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_490,plain,
% 7.03/1.50      ( sP0(sK7,sK10,sK6)
% 7.03/1.50      | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 7.03/1.50      | ~ l1_orders_2(sK7)
% 7.03/1.50      | ~ l1_orders_2(sK6)
% 7.03/1.50      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 7.03/1.50      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 7.03/1.50      inference(unflattening,[status(thm)],[c_489]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_25,negated_conjecture,
% 7.03/1.50      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
% 7.03/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_492,plain,
% 7.03/1.50      ( sP0(sK7,sK10,sK6)
% 7.03/1.50      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 7.03/1.50      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 7.03/1.50      inference(global_propositional_subsumption,
% 7.03/1.50                [status(thm)],
% 7.03/1.50                [c_490,c_31,c_30,c_25]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_1044,plain,
% 7.03/1.50      ( sP0(sK7,sK10,sK6) ),
% 7.03/1.50      inference(equality_resolution_simp,[status(thm)],[c_492]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_1047,plain,
% 7.03/1.50      ( sP0(sK7,sK10,sK6) ),
% 7.03/1.50      inference(global_propositional_subsumption,
% 7.03/1.50                [status(thm)],
% 7.03/1.50                [c_473,c_1044]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2441,plain,
% 7.03/1.50      ( sP0(sK7,sK10,sK6) = iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_1047]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_2472,plain,
% 7.03/1.50      ( sP0(sK7,sK11,sK6) = iProver_top ),
% 7.03/1.50      inference(light_normalisation,[status(thm)],[c_2441,c_19]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_6,plain,
% 7.03/1.50      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2)) | sP0(X0,X1,X2) ),
% 7.03/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_863,plain,
% 7.03/1.50      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2))
% 7.03/1.50      | u1_struct_0(sK9) != u1_struct_0(sK9)
% 7.03/1.50      | u1_struct_0(sK8) != u1_struct_0(sK8)
% 7.03/1.50      | sK9 != X0
% 7.03/1.50      | sK8 != X2
% 7.03/1.50      | sK11 != X1 ),
% 7.03/1.50      inference(resolution_lifted,[status(thm)],[c_6,c_435]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_864,plain,
% 7.03/1.50      ( ~ r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) ),
% 7.03/1.50      inference(unflattening,[status(thm)],[c_863]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_865,plain,
% 7.03/1.50      ( r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) != iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_864]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_798,plain,
% 7.03/1.50      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
% 7.03/1.50      | u1_struct_0(sK9) != u1_struct_0(sK9)
% 7.03/1.50      | u1_struct_0(sK8) != u1_struct_0(sK8)
% 7.03/1.50      | sK9 != X0
% 7.03/1.50      | sK8 != X2
% 7.03/1.50      | sK11 != X1 ),
% 7.03/1.50      inference(resolution_lifted,[status(thm)],[c_9,c_435]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_799,plain,
% 7.03/1.50      ( m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) ),
% 7.03/1.50      inference(unflattening,[status(thm)],[c_798]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_800,plain,
% 7.03/1.50      ( m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) = iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_10,plain,
% 7.03/1.50      ( sP0(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ),
% 7.03/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_775,plain,
% 7.03/1.50      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
% 7.03/1.50      | u1_struct_0(sK9) != u1_struct_0(sK9)
% 7.03/1.50      | u1_struct_0(sK8) != u1_struct_0(sK8)
% 7.03/1.50      | sK9 != X0
% 7.03/1.50      | sK8 != X2
% 7.03/1.50      | sK11 != X1 ),
% 7.03/1.50      inference(resolution_lifted,[status(thm)],[c_10,c_435]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_776,plain,
% 7.03/1.50      ( m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) ),
% 7.03/1.50      inference(unflattening,[status(thm)],[c_775]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(c_777,plain,
% 7.03/1.50      ( m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) = iProver_top ),
% 7.03/1.50      inference(predicate_to_equality,[status(thm)],[c_776]) ).
% 7.03/1.50  
% 7.03/1.50  cnf(contradiction,plain,
% 7.03/1.50      ( $false ),
% 7.03/1.50      inference(minisat,
% 7.03/1.50                [status(thm)],
% 7.03/1.50                [c_24172,c_2472,c_1053,c_865,c_800,c_777]) ).
% 7.03/1.50  
% 7.03/1.50  
% 7.03/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.03/1.50  
% 7.03/1.50  ------                               Statistics
% 7.03/1.50  
% 7.03/1.50  ------ General
% 7.03/1.50  
% 7.03/1.50  abstr_ref_over_cycles:                  0
% 7.03/1.50  abstr_ref_under_cycles:                 0
% 7.03/1.50  gc_basic_clause_elim:                   0
% 7.03/1.50  forced_gc_time:                         0
% 7.03/1.50  parsing_time:                           0.011
% 7.03/1.50  unif_index_cands_time:                  0.
% 7.03/1.50  unif_index_add_time:                    0.
% 7.03/1.50  orderings_time:                         0.
% 7.03/1.50  out_proof_time:                         0.016
% 7.03/1.50  total_time:                             0.695
% 7.03/1.50  num_of_symbols:                         56
% 7.03/1.50  num_of_terms:                           21580
% 7.03/1.50  
% 7.03/1.50  ------ Preprocessing
% 7.03/1.50  
% 7.03/1.50  num_of_splits:                          0
% 7.03/1.50  num_of_split_atoms:                     0
% 7.03/1.50  num_of_reused_defs:                     0
% 7.03/1.50  num_eq_ax_congr_red:                    62
% 7.03/1.50  num_of_sem_filtered_clauses:            1
% 7.03/1.50  num_of_subtypes:                        0
% 7.03/1.50  monotx_restored_types:                  0
% 7.03/1.50  sat_num_of_epr_types:                   0
% 7.03/1.50  sat_num_of_non_cyclic_types:            0
% 7.03/1.50  sat_guarded_non_collapsed_types:        0
% 7.03/1.50  num_pure_diseq_elim:                    0
% 7.03/1.50  simp_replaced_by:                       0
% 7.03/1.50  res_preprocessed:                       163
% 7.03/1.50  prep_upred:                             0
% 7.03/1.50  prep_unflattend:                        196
% 7.03/1.50  smt_new_axioms:                         0
% 7.03/1.50  pred_elim_cands:                        4
% 7.03/1.50  pred_elim:                              4
% 7.03/1.50  pred_elim_cl:                           4
% 7.03/1.50  pred_elim_cycles:                       7
% 7.03/1.50  merged_defs:                            0
% 7.03/1.50  merged_defs_ncl:                        0
% 7.03/1.50  bin_hyper_res:                          0
% 7.03/1.50  prep_cycles:                            5
% 7.03/1.50  pred_elim_time:                         0.028
% 7.03/1.50  splitting_time:                         0.
% 7.03/1.50  sem_filter_time:                        0.
% 7.03/1.50  monotx_time:                            0.
% 7.03/1.50  subtype_inf_time:                       0.
% 7.03/1.50  
% 7.03/1.50  ------ Problem properties
% 7.03/1.50  
% 7.03/1.50  clauses:                                26
% 7.03/1.50  conjectures:                            9
% 7.03/1.50  epr:                                    8
% 7.03/1.50  horn:                                   19
% 7.03/1.50  ground:                                 12
% 7.03/1.50  unary:                                  11
% 7.03/1.50  binary:                                 11
% 7.03/1.50  lits:                                   55
% 7.03/1.50  lits_eq:                                13
% 7.03/1.50  fd_pure:                                0
% 7.03/1.50  fd_pseudo:                              0
% 7.03/1.50  fd_cond:                                0
% 7.03/1.50  fd_pseudo_cond:                         2
% 7.03/1.50  ac_symbols:                             0
% 7.03/1.50  
% 7.03/1.50  ------ Propositional Solver
% 7.03/1.50  
% 7.03/1.50  prop_solver_calls:                      35
% 7.03/1.50  prop_fast_solver_calls:                 2970
% 7.03/1.50  smt_solver_calls:                       0
% 7.03/1.50  smt_fast_solver_calls:                  0
% 7.03/1.50  prop_num_of_clauses:                    6064
% 7.03/1.50  prop_preprocess_simplified:             12358
% 7.03/1.50  prop_fo_subsumed:                       80
% 7.03/1.50  prop_solver_time:                       0.
% 7.03/1.50  smt_solver_time:                        0.
% 7.03/1.50  smt_fast_solver_time:                   0.
% 7.03/1.50  prop_fast_solver_time:                  0.
% 7.03/1.50  prop_unsat_core_time:                   0.
% 7.03/1.50  
% 7.03/1.50  ------ QBF
% 7.03/1.50  
% 7.03/1.50  qbf_q_res:                              0
% 7.03/1.50  qbf_num_tautologies:                    0
% 7.03/1.50  qbf_prep_cycles:                        0
% 7.03/1.50  
% 7.03/1.50  ------ BMC1
% 7.03/1.50  
% 7.03/1.50  bmc1_current_bound:                     -1
% 7.03/1.50  bmc1_last_solved_bound:                 -1
% 7.03/1.50  bmc1_unsat_core_size:                   -1
% 7.03/1.50  bmc1_unsat_core_parents_size:           -1
% 7.03/1.50  bmc1_merge_next_fun:                    0
% 7.03/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.03/1.50  
% 7.03/1.50  ------ Instantiation
% 7.03/1.50  
% 7.03/1.50  inst_num_of_clauses:                    1775
% 7.03/1.50  inst_num_in_passive:                    217
% 7.03/1.50  inst_num_in_active:                     1151
% 7.03/1.50  inst_num_in_unprocessed:                415
% 7.03/1.50  inst_num_of_loops:                      1180
% 7.03/1.50  inst_num_of_learning_restarts:          0
% 7.03/1.50  inst_num_moves_active_passive:          23
% 7.03/1.50  inst_lit_activity:                      0
% 7.03/1.50  inst_lit_activity_moves:                0
% 7.03/1.50  inst_num_tautologies:                   0
% 7.03/1.50  inst_num_prop_implied:                  0
% 7.03/1.50  inst_num_existing_simplified:           0
% 7.03/1.50  inst_num_eq_res_simplified:             0
% 7.03/1.50  inst_num_child_elim:                    0
% 7.03/1.50  inst_num_of_dismatching_blockings:      2239
% 7.03/1.50  inst_num_of_non_proper_insts:           3357
% 7.03/1.50  inst_num_of_duplicates:                 0
% 7.03/1.50  inst_inst_num_from_inst_to_res:         0
% 7.03/1.50  inst_dismatching_checking_time:         0.
% 7.03/1.50  
% 7.03/1.50  ------ Resolution
% 7.03/1.50  
% 7.03/1.50  res_num_of_clauses:                     0
% 7.03/1.50  res_num_in_passive:                     0
% 7.03/1.50  res_num_in_active:                      0
% 7.03/1.50  res_num_of_loops:                       168
% 7.03/1.50  res_forward_subset_subsumed:            371
% 7.03/1.50  res_backward_subset_subsumed:           26
% 7.03/1.50  res_forward_subsumed:                   0
% 7.03/1.50  res_backward_subsumed:                  2
% 7.03/1.50  res_forward_subsumption_resolution:     0
% 7.03/1.50  res_backward_subsumption_resolution:    0
% 7.03/1.50  res_clause_to_clause_subsumption:       1733
% 7.03/1.50  res_orphan_elimination:                 0
% 7.03/1.50  res_tautology_del:                      299
% 7.03/1.50  res_num_eq_res_simplified:              2
% 7.03/1.50  res_num_sel_changes:                    0
% 7.03/1.50  res_moves_from_active_to_pass:          0
% 7.03/1.50  
% 7.03/1.50  ------ Superposition
% 7.03/1.50  
% 7.03/1.50  sup_time_total:                         0.
% 7.03/1.50  sup_time_generating:                    0.
% 7.03/1.50  sup_time_sim_full:                      0.
% 7.03/1.50  sup_time_sim_immed:                     0.
% 7.03/1.50  
% 7.03/1.50  sup_num_of_clauses:                     346
% 7.03/1.50  sup_num_in_active:                      213
% 7.03/1.50  sup_num_in_passive:                     133
% 7.03/1.50  sup_num_of_loops:                       235
% 7.03/1.50  sup_fw_superposition:                   328
% 7.03/1.50  sup_bw_superposition:                   214
% 7.03/1.50  sup_immediate_simplified:               285
% 7.03/1.50  sup_given_eliminated:                   2
% 7.03/1.50  comparisons_done:                       0
% 7.03/1.50  comparisons_avoided:                    0
% 7.03/1.50  
% 7.03/1.50  ------ Simplifications
% 7.03/1.50  
% 7.03/1.50  
% 7.03/1.50  sim_fw_subset_subsumed:                 34
% 7.03/1.50  sim_bw_subset_subsumed:                 20
% 7.03/1.50  sim_fw_subsumed:                        42
% 7.03/1.50  sim_bw_subsumed:                        1
% 7.03/1.50  sim_fw_subsumption_res:                 15
% 7.03/1.50  sim_bw_subsumption_res:                 0
% 7.03/1.50  sim_tautology_del:                      38
% 7.03/1.50  sim_eq_tautology_del:                   12
% 7.03/1.50  sim_eq_res_simp:                        6
% 7.03/1.50  sim_fw_demodulated:                     3
% 7.03/1.50  sim_bw_demodulated:                     25
% 7.03/1.50  sim_light_normalised:                   270
% 7.03/1.50  sim_joinable_taut:                      0
% 7.03/1.50  sim_joinable_simp:                      0
% 7.03/1.50  sim_ac_normalised:                      0
% 7.03/1.50  sim_smt_subsumption:                    0
% 7.03/1.50  
%------------------------------------------------------------------------------
