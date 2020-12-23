%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:37 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  204 (2168 expanded)
%              Number of clauses        :  137 ( 451 expanded)
%              Number of leaves         :   17 ( 882 expanded)
%              Depth                    :   25
%              Number of atoms          :  884 (29229 expanded)
%              Number of equality atoms :  376 (6872 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,plain,(
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
    inference(nnf_transformation,[],[f15])).

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

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f13,plain,(
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
    inference(flattening,[],[f13])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f14,f33,f32,f31,f30,f29,f28])).

fof(f62,plain,(
    g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f34])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f61,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(flattening,[],[f11])).

fof(f16,plain,(
    ! [X0,X2,X1] :
      ( ( v5_orders_3(X2,X0,X1)
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f12,f16,f15])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f34])).

fof(f19,plain,(
    ! [X0,X2,X1] :
      ( ( ( v5_orders_3(X2,X0,X1)
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ v5_orders_3(X2,X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f16])).

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

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | k1_funct_1(X1,sK3(X0,X1,X2)) = sK5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    sK10 = sK11 ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f34])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | ~ v5_orders_3(X1,X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    v5_orders_3(sK10,sK6,sK7) ),
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

fof(f67,plain,(
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

fof(f68,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r1_orders_2(X0,k1_funct_1(X1,X7),k1_funct_1(X1,X8))
      | ~ m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0))
      | ~ m1_subset_1(k1_funct_1(X1,X7),u1_struct_0(X0))
      | ~ r1_orders_2(X2,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f67])).

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

cnf(c_12,plain,
    ( sP0(X0,X1,X2)
    | r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_789,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_800,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_21,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_798,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2416,plain,
    ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK6) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_798])).

cnf(c_31,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_85,plain,
    ( m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2418,plain,
    ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK6) = X1
    | m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_798])).

cnf(c_2453,plain,
    ( ~ m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
    | g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK6) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2418])).

cnf(c_2789,plain,
    ( u1_orders_2(sK6) = X1
    | g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2416,c_31,c_85,c_2453])).

cnf(c_2790,plain,
    ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK6) = X1 ),
    inference(renaming,[status(thm)],[c_2789])).

cnf(c_2796,plain,
    ( u1_orders_2(sK8) = u1_orders_2(sK6) ),
    inference(equality_resolution,[status(thm)],[c_2790])).

cnf(c_0,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_801,plain,
    ( r1_orders_2(X0,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5739,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK8)) != iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2796,c_801])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_797,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2308,plain,
    ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK6) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_797])).

cnf(c_32,plain,
    ( l1_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_84,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_86,plain,
    ( m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) = iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_2310,plain,
    ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK6) = X0
    | m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_797])).

cnf(c_2562,plain,
    ( u1_struct_0(sK6) = X0
    | g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2308,c_32,c_86,c_2310])).

cnf(c_2563,plain,
    ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK6) = X0 ),
    inference(renaming,[status(thm)],[c_2562])).

cnf(c_2569,plain,
    ( u1_struct_0(sK8) = u1_struct_0(sK6) ),
    inference(equality_resolution,[status(thm)],[c_2563])).

cnf(c_5761,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK8)) != iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5739,c_2569])).

cnf(c_11045,plain,
    ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r1_orders_2(sK6,X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5761,c_32])).

cnf(c_11046,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11045])).

cnf(c_11055,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_800,c_11046])).

cnf(c_29,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_34,plain,
    ( l1_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11320,plain,
    ( m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r1_orders_2(sK8,X0,X1) != iProver_top
    | r1_orders_2(sK6,X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11055,c_34])).

cnf(c_11321,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11320])).

cnf(c_11330,plain,
    ( sP0(X0,X1,sK8) = iProver_top
    | r1_orders_2(sK6,sK2(X0,X1,sK8),sK3(X0,X1,sK8)) = iProver_top
    | m1_subset_1(sK2(X0,X1,sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK3(X0,X1,sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_789,c_11321])).

cnf(c_13,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_788,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_787,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11375,plain,
    ( sP0(X0,X1,sK8) = iProver_top
    | r1_orders_2(sK6,sK2(X0,X1,sK8),sK3(X0,X1,sK8)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11330,c_788,c_787])).

cnf(c_9,plain,
    ( sP0(X0,X1,X2)
    | k1_funct_1(X1,sK2(X0,X1,X2)) = sK4(X0,X1,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_792,plain,
    ( k1_funct_1(X0,sK2(X1,X0,X2)) = sK4(X1,X0,X2)
    | sP0(X1,X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_782,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | sP1(X1,X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_785,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | sP1(X1,X0,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1579,plain,
    ( v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) != iProver_top
    | sP1(sK8,sK11,sK9) = iProver_top
    | v1_funct_1(sK11) != iProver_top
    | l1_orders_2(sK9) != iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_782,c_785])).

cnf(c_28,negated_conjecture,
    ( l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_35,plain,
    ( l1_orders_2(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_39,plain,
    ( v1_funct_1(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_40,plain,
    ( v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_41,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1096,plain,
    ( ~ v1_funct_2(sK11,u1_struct_0(X0),u1_struct_0(X1))
    | sP1(X0,sK11,X1)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK11)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1226,plain,
    ( ~ v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9))
    | sP1(sK8,sK11,sK9)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
    | ~ v1_funct_1(sK11)
    | ~ l1_orders_2(sK9)
    | ~ l1_orders_2(sK8) ),
    inference(instantiation,[status(thm)],[c_1096])).

cnf(c_1227,plain,
    ( v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) != iProver_top
    | sP1(sK8,sK11,sK9) = iProver_top
    | m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | l1_orders_2(sK9) != iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1226])).

cnf(c_3098,plain,
    ( sP1(sK8,sK11,sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1579,c_34,c_35,c_39,c_40,c_41,c_1227])).

cnf(c_5,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | v5_orders_3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_796,plain,
    ( sP1(X0,X1,X2) != iProver_top
    | sP0(X2,X1,X0) != iProver_top
    | v5_orders_3(X1,X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3103,plain,
    ( sP0(sK9,sK11,sK8) != iProver_top
    | v5_orders_3(sK11,sK8,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_3098,c_796])).

cnf(c_17,negated_conjecture,
    ( ~ v5_orders_3(sK11,sK8,sK9) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_43,plain,
    ( v5_orders_3(sK11,sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1254,plain,
    ( ~ sP1(sK8,sK11,sK9)
    | ~ sP0(sK9,sK11,sK8)
    | v5_orders_3(sK11,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1255,plain,
    ( sP1(sK8,sK11,sK9) != iProver_top
    | sP0(sK9,sK11,sK8) != iProver_top
    | v5_orders_3(sK11,sK8,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1254])).

cnf(c_3246,plain,
    ( sP0(sK9,sK11,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3103,c_34,c_35,c_39,c_40,c_41,c_43,c_1227,c_1255])).

cnf(c_3252,plain,
    ( k1_funct_1(sK11,sK2(sK9,sK11,sK8)) = sK4(sK9,sK11,sK8) ),
    inference(superposition,[status(thm)],[c_792,c_3246])).

cnf(c_8,plain,
    ( sP0(X0,X1,X2)
    | k1_funct_1(X1,sK3(X0,X1,X2)) = sK5(X0,X1,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_793,plain,
    ( k1_funct_1(X0,sK3(X1,X0,X2)) = sK5(X1,X0,X2)
    | sP0(X1,X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3251,plain,
    ( k1_funct_1(sK11,sK3(sK9,sK11,sK8)) = sK5(sK9,sK11,sK8) ),
    inference(superposition,[status(thm)],[c_793,c_3246])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_779,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19,negated_conjecture,
    ( sK10 = sK11 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_825,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_779,c_19])).

cnf(c_1580,plain,
    ( v1_funct_2(sK11,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | sP1(sK6,sK11,sK7) = iProver_top
    | v1_funct_1(sK11) != iProver_top
    | l1_orders_2(sK7) != iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_825,c_785])).

cnf(c_30,negated_conjecture,
    ( l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_33,plain,
    ( l1_orders_2(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_778,plain,
    ( v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_820,plain,
    ( v1_funct_2(sK11,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_778,c_19])).

cnf(c_3258,plain,
    ( sP1(sK6,sK11,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1580,c_32,c_33,c_39,c_820])).

cnf(c_6,plain,
    ( ~ sP1(X0,X1,X2)
    | sP0(X2,X1,X0)
    | ~ v5_orders_3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_795,plain,
    ( sP1(X0,X1,X2) != iProver_top
    | sP0(X2,X1,X0) = iProver_top
    | v5_orders_3(X1,X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3264,plain,
    ( sP0(sK7,sK11,sK6) = iProver_top
    | v5_orders_3(sK11,sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3258,c_795])).

cnf(c_18,negated_conjecture,
    ( v5_orders_3(sK10,sK6,sK7) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_783,plain,
    ( v5_orders_3(sK10,sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_815,plain,
    ( v5_orders_3(sK11,sK6,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_783,c_19])).

cnf(c_3513,plain,
    ( sP0(sK7,sK11,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3264,c_815])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X3,X4)
    | r1_orders_2(X0,k1_funct_1(X1,X3),k1_funct_1(X1,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(k1_funct_1(X1,X4),u1_struct_0(X0))
    | ~ m1_subset_1(k1_funct_1(X1,X3),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_786,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r1_orders_2(X2,X3,X4) != iProver_top
    | r1_orders_2(X0,k1_funct_1(X1,X3),k1_funct_1(X1,X4)) = iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(k1_funct_1(X1,X4),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k1_funct_1(X1,X3),u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3518,plain,
    ( r1_orders_2(sK7,k1_funct_1(sK11,X0),k1_funct_1(sK11,X1)) = iProver_top
    | r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,X1),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3513,c_786])).

cnf(c_20,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2307,plain,
    ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK7) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_797])).

cnf(c_2462,plain,
    ( u1_struct_0(sK9) = u1_struct_0(sK7)
    | m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2307])).

cnf(c_2474,plain,
    ( ~ m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
    | u1_struct_0(sK9) = u1_struct_0(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2462])).

cnf(c_2914,plain,
    ( m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
    | ~ l1_orders_2(sK9) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3523,plain,
    ( u1_struct_0(sK9) = u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2462,c_28,c_2474,c_2914])).

cnf(c_6287,plain,
    ( r1_orders_2(sK7,k1_funct_1(sK11,X0),k1_funct_1(sK11,X1)) = iProver_top
    | r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,X1),u1_struct_0(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3518,c_2569,c_3523])).

cnf(c_6300,plain,
    ( r1_orders_2(sK7,k1_funct_1(sK11,X0),sK5(sK9,sK11,sK8)) = iProver_top
    | r1_orders_2(sK6,X0,sK3(sK9,sK11,sK8)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK3(sK9,sK11,sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,sK3(sK9,sK11,sK8)),u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3251,c_6287])).

cnf(c_6351,plain,
    ( r1_orders_2(sK7,k1_funct_1(sK11,X0),sK5(sK9,sK11,sK8)) = iProver_top
    | r1_orders_2(sK6,X0,sK3(sK9,sK11,sK8)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK3(sK9,sK11,sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6300,c_3251])).

cnf(c_10,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1394,plain,
    ( sP0(sK9,sK11,sK8)
    | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1395,plain,
    ( sP0(sK9,sK11,sK8) = iProver_top
    | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1394])).

cnf(c_1392,plain,
    ( sP0(sK9,sK11,sK8)
    | m1_subset_1(sK3(sK9,sK11,sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1399,plain,
    ( sP0(sK9,sK11,sK8) = iProver_top
    | m1_subset_1(sK3(sK9,sK11,sK8),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1392])).

cnf(c_13741,plain,
    ( r1_orders_2(sK7,k1_funct_1(sK11,X0),sK5(sK9,sK11,sK8)) = iProver_top
    | r1_orders_2(sK6,X0,sK3(sK9,sK11,sK8)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6351,c_34,c_35,c_39,c_40,c_41,c_43,c_1227,c_1255,c_1395,c_1399])).

cnf(c_13751,plain,
    ( r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
    | r1_orders_2(sK6,sK2(sK9,sK11,sK8),sK3(sK9,sK11,sK8)) != iProver_top
    | m1_subset_1(sK2(sK9,sK11,sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k1_funct_1(sK11,sK2(sK9,sK11,sK8)),u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3252,c_13741])).

cnf(c_13804,plain,
    ( r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
    | r1_orders_2(sK6,sK2(sK9,sK11,sK8),sK3(sK9,sK11,sK8)) != iProver_top
    | m1_subset_1(sK2(sK9,sK11,sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13751,c_3252])).

cnf(c_11,plain,
    ( sP0(X0,X1,X2)
    | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1393,plain,
    ( sP0(sK9,sK11,sK8)
    | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1397,plain,
    ( sP0(sK9,sK11,sK8) = iProver_top
    | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1393])).

cnf(c_1391,plain,
    ( sP0(sK9,sK11,sK8)
    | m1_subset_1(sK2(sK9,sK11,sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1401,plain,
    ( sP0(sK9,sK11,sK8) = iProver_top
    | m1_subset_1(sK2(sK9,sK11,sK8),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1391])).

cnf(c_13992,plain,
    ( r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
    | r1_orders_2(sK6,sK2(sK9,sK11,sK8),sK3(sK9,sK11,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13804,c_34,c_35,c_39,c_40,c_41,c_43,c_1227,c_1255,c_1397,c_1401])).

cnf(c_13998,plain,
    ( sP0(sK9,sK11,sK8) = iProver_top
    | r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11375,c_13992])).

cnf(c_14254,plain,
    ( r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13998,c_34,c_35,c_39,c_40,c_41,c_43,c_1227,c_1255])).

cnf(c_790,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2415,plain,
    ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK7) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_798])).

cnf(c_2646,plain,
    ( u1_orders_2(sK9) = u1_orders_2(sK7)
    | m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2415])).

cnf(c_2662,plain,
    ( ~ m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
    | u1_orders_2(sK9) = u1_orders_2(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2646])).

cnf(c_4629,plain,
    ( u1_orders_2(sK9) = u1_orders_2(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2646,c_28,c_2662,c_2914])).

cnf(c_4648,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK9)) = iProver_top
    | l1_orders_2(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4629,c_800])).

cnf(c_4658,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK9)) = iProver_top
    | l1_orders_2(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4648,c_3523])).

cnf(c_8031,plain,
    ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK9)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | r1_orders_2(sK7,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4658,c_33])).

cnf(c_8032,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK9)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8031])).

cnf(c_8041,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | r1_orders_2(sK9,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | l1_orders_2(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_8032,c_801])).

cnf(c_8214,plain,
    ( m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | r1_orders_2(sK9,X0,X1) = iProver_top
    | r1_orders_2(sK7,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8041,c_35])).

cnf(c_8215,plain,
    ( r1_orders_2(sK7,X0,X1) != iProver_top
    | r1_orders_2(sK9,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8214])).

cnf(c_8225,plain,
    ( sP0(sK9,X0,X1) = iProver_top
    | r1_orders_2(sK7,sK4(sK9,X0,X1),X2) != iProver_top
    | r1_orders_2(sK9,sK4(sK9,X0,X1),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_8215])).

cnf(c_14261,plain,
    ( sP0(sK9,sK11,sK8) = iProver_top
    | r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
    | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14254,c_8225])).

cnf(c_7,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1388,plain,
    ( sP0(sK9,sK11,sK8)
    | ~ r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1407,plain,
    ( sP0(sK9,sK11,sK8) = iProver_top
    | r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1388])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14261,c_1407,c_1395,c_1255,c_1227,c_43,c_41,c_40,c_39,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.93/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.93/1.00  
% 3.93/1.00  ------  iProver source info
% 3.93/1.00  
% 3.93/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.93/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.93/1.00  git: non_committed_changes: false
% 3.93/1.00  git: last_make_outside_of_git: false
% 3.93/1.00  
% 3.93/1.00  ------ 
% 3.93/1.00  
% 3.93/1.00  ------ Input Options
% 3.93/1.00  
% 3.93/1.00  --out_options                           all
% 3.93/1.00  --tptp_safe_out                         true
% 3.93/1.00  --problem_path                          ""
% 3.93/1.00  --include_path                          ""
% 3.93/1.00  --clausifier                            res/vclausify_rel
% 3.93/1.00  --clausifier_options                    --mode clausify
% 3.93/1.00  --stdin                                 false
% 3.93/1.00  --stats_out                             sel
% 3.93/1.00  
% 3.93/1.00  ------ General Options
% 3.93/1.00  
% 3.93/1.00  --fof                                   false
% 3.93/1.00  --time_out_real                         604.99
% 3.93/1.00  --time_out_virtual                      -1.
% 3.93/1.00  --symbol_type_check                     false
% 3.93/1.00  --clausify_out                          false
% 3.93/1.00  --sig_cnt_out                           false
% 3.93/1.00  --trig_cnt_out                          false
% 3.93/1.00  --trig_cnt_out_tolerance                1.
% 3.93/1.00  --trig_cnt_out_sk_spl                   false
% 3.93/1.00  --abstr_cl_out                          false
% 3.93/1.00  
% 3.93/1.00  ------ Global Options
% 3.93/1.00  
% 3.93/1.00  --schedule                              none
% 3.93/1.00  --add_important_lit                     false
% 3.93/1.00  --prop_solver_per_cl                    1000
% 3.93/1.00  --min_unsat_core                        false
% 3.93/1.00  --soft_assumptions                      false
% 3.93/1.00  --soft_lemma_size                       3
% 3.93/1.00  --prop_impl_unit_size                   0
% 3.93/1.00  --prop_impl_unit                        []
% 3.93/1.00  --share_sel_clauses                     true
% 3.93/1.00  --reset_solvers                         false
% 3.93/1.00  --bc_imp_inh                            [conj_cone]
% 3.93/1.00  --conj_cone_tolerance                   3.
% 3.93/1.00  --extra_neg_conj                        none
% 3.93/1.00  --large_theory_mode                     true
% 3.93/1.00  --prolific_symb_bound                   200
% 3.93/1.00  --lt_threshold                          2000
% 3.93/1.00  --clause_weak_htbl                      true
% 3.93/1.00  --gc_record_bc_elim                     false
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing Options
% 3.93/1.00  
% 3.93/1.00  --preprocessing_flag                    true
% 3.93/1.00  --time_out_prep_mult                    0.1
% 3.93/1.00  --splitting_mode                        input
% 3.93/1.00  --splitting_grd                         true
% 3.93/1.00  --splitting_cvd                         false
% 3.93/1.00  --splitting_cvd_svl                     false
% 3.93/1.00  --splitting_nvd                         32
% 3.93/1.00  --sub_typing                            true
% 3.93/1.00  --prep_gs_sim                           false
% 3.93/1.00  --prep_unflatten                        true
% 3.93/1.00  --prep_res_sim                          true
% 3.93/1.00  --prep_upred                            true
% 3.93/1.00  --prep_sem_filter                       exhaustive
% 3.93/1.00  --prep_sem_filter_out                   false
% 3.93/1.00  --pred_elim                             false
% 3.93/1.00  --res_sim_input                         true
% 3.93/1.00  --eq_ax_congr_red                       true
% 3.93/1.00  --pure_diseq_elim                       true
% 3.93/1.00  --brand_transform                       false
% 3.93/1.00  --non_eq_to_eq                          false
% 3.93/1.00  --prep_def_merge                        true
% 3.93/1.00  --prep_def_merge_prop_impl              false
% 3.93/1.00  --prep_def_merge_mbd                    true
% 3.93/1.00  --prep_def_merge_tr_red                 false
% 3.93/1.00  --prep_def_merge_tr_cl                  false
% 3.93/1.00  --smt_preprocessing                     true
% 3.93/1.00  --smt_ac_axioms                         fast
% 3.93/1.00  --preprocessed_out                      false
% 3.93/1.00  --preprocessed_stats                    false
% 3.93/1.00  
% 3.93/1.00  ------ Abstraction refinement Options
% 3.93/1.00  
% 3.93/1.00  --abstr_ref                             []
% 3.93/1.00  --abstr_ref_prep                        false
% 3.93/1.00  --abstr_ref_until_sat                   false
% 3.93/1.00  --abstr_ref_sig_restrict                funpre
% 3.93/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.93/1.00  --abstr_ref_under                       []
% 3.93/1.00  
% 3.93/1.00  ------ SAT Options
% 3.93/1.00  
% 3.93/1.00  --sat_mode                              false
% 3.93/1.00  --sat_fm_restart_options                ""
% 3.93/1.00  --sat_gr_def                            false
% 3.93/1.00  --sat_epr_types                         true
% 3.93/1.00  --sat_non_cyclic_types                  false
% 3.93/1.00  --sat_finite_models                     false
% 3.93/1.00  --sat_fm_lemmas                         false
% 3.93/1.00  --sat_fm_prep                           false
% 3.93/1.00  --sat_fm_uc_incr                        true
% 3.93/1.00  --sat_out_model                         small
% 3.93/1.00  --sat_out_clauses                       false
% 3.93/1.00  
% 3.93/1.00  ------ QBF Options
% 3.93/1.00  
% 3.93/1.00  --qbf_mode                              false
% 3.93/1.00  --qbf_elim_univ                         false
% 3.93/1.00  --qbf_dom_inst                          none
% 3.93/1.00  --qbf_dom_pre_inst                      false
% 3.93/1.00  --qbf_sk_in                             false
% 3.93/1.00  --qbf_pred_elim                         true
% 3.93/1.00  --qbf_split                             512
% 3.93/1.00  
% 3.93/1.00  ------ BMC1 Options
% 3.93/1.00  
% 3.93/1.00  --bmc1_incremental                      false
% 3.93/1.00  --bmc1_axioms                           reachable_all
% 3.93/1.00  --bmc1_min_bound                        0
% 3.93/1.00  --bmc1_max_bound                        -1
% 3.93/1.00  --bmc1_max_bound_default                -1
% 3.93/1.00  --bmc1_symbol_reachability              true
% 3.93/1.00  --bmc1_property_lemmas                  false
% 3.93/1.00  --bmc1_k_induction                      false
% 3.93/1.00  --bmc1_non_equiv_states                 false
% 3.93/1.00  --bmc1_deadlock                         false
% 3.93/1.00  --bmc1_ucm                              false
% 3.93/1.00  --bmc1_add_unsat_core                   none
% 3.93/1.00  --bmc1_unsat_core_children              false
% 3.93/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.93/1.00  --bmc1_out_stat                         full
% 3.93/1.00  --bmc1_ground_init                      false
% 3.93/1.00  --bmc1_pre_inst_next_state              false
% 3.93/1.00  --bmc1_pre_inst_state                   false
% 3.93/1.00  --bmc1_pre_inst_reach_state             false
% 3.93/1.00  --bmc1_out_unsat_core                   false
% 3.93/1.00  --bmc1_aig_witness_out                  false
% 3.93/1.00  --bmc1_verbose                          false
% 3.93/1.00  --bmc1_dump_clauses_tptp                false
% 3.93/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.93/1.00  --bmc1_dump_file                        -
% 3.93/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.93/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.93/1.00  --bmc1_ucm_extend_mode                  1
% 3.93/1.00  --bmc1_ucm_init_mode                    2
% 3.93/1.00  --bmc1_ucm_cone_mode                    none
% 3.93/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.93/1.00  --bmc1_ucm_relax_model                  4
% 3.93/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.93/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.93/1.00  --bmc1_ucm_layered_model                none
% 3.93/1.00  --bmc1_ucm_max_lemma_size               10
% 3.93/1.00  
% 3.93/1.00  ------ AIG Options
% 3.93/1.00  
% 3.93/1.00  --aig_mode                              false
% 3.93/1.00  
% 3.93/1.00  ------ Instantiation Options
% 3.93/1.00  
% 3.93/1.00  --instantiation_flag                    true
% 3.93/1.00  --inst_sos_flag                         false
% 3.93/1.00  --inst_sos_phase                        true
% 3.93/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.93/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.93/1.00  --inst_lit_sel_side                     num_symb
% 3.93/1.00  --inst_solver_per_active                1400
% 3.93/1.00  --inst_solver_calls_frac                1.
% 3.93/1.00  --inst_passive_queue_type               priority_queues
% 3.93/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.93/1.00  --inst_passive_queues_freq              [25;2]
% 3.93/1.00  --inst_dismatching                      true
% 3.93/1.00  --inst_eager_unprocessed_to_passive     true
% 3.93/1.00  --inst_prop_sim_given                   true
% 3.93/1.00  --inst_prop_sim_new                     false
% 3.93/1.00  --inst_subs_new                         false
% 3.93/1.00  --inst_eq_res_simp                      false
% 3.93/1.00  --inst_subs_given                       false
% 3.93/1.00  --inst_orphan_elimination               true
% 3.93/1.00  --inst_learning_loop_flag               true
% 3.93/1.00  --inst_learning_start                   3000
% 3.93/1.00  --inst_learning_factor                  2
% 3.93/1.00  --inst_start_prop_sim_after_learn       3
% 3.93/1.00  --inst_sel_renew                        solver
% 3.93/1.00  --inst_lit_activity_flag                true
% 3.93/1.00  --inst_restr_to_given                   false
% 3.93/1.00  --inst_activity_threshold               500
% 3.93/1.00  --inst_out_proof                        true
% 3.93/1.00  
% 3.93/1.00  ------ Resolution Options
% 3.93/1.00  
% 3.93/1.00  --resolution_flag                       true
% 3.93/1.00  --res_lit_sel                           adaptive
% 3.93/1.00  --res_lit_sel_side                      none
% 3.93/1.00  --res_ordering                          kbo
% 3.93/1.00  --res_to_prop_solver                    active
% 3.93/1.00  --res_prop_simpl_new                    false
% 3.93/1.00  --res_prop_simpl_given                  true
% 3.93/1.00  --res_passive_queue_type                priority_queues
% 3.93/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.93/1.00  --res_passive_queues_freq               [15;5]
% 3.93/1.00  --res_forward_subs                      full
% 3.93/1.00  --res_backward_subs                     full
% 3.93/1.00  --res_forward_subs_resolution           true
% 3.93/1.00  --res_backward_subs_resolution          true
% 3.93/1.00  --res_orphan_elimination                true
% 3.93/1.00  --res_time_limit                        2.
% 3.93/1.00  --res_out_proof                         true
% 3.93/1.00  
% 3.93/1.00  ------ Superposition Options
% 3.93/1.00  
% 3.93/1.00  --superposition_flag                    true
% 3.93/1.00  --sup_passive_queue_type                priority_queues
% 3.93/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.93/1.00  --sup_passive_queues_freq               [1;4]
% 3.93/1.00  --demod_completeness_check              fast
% 3.93/1.00  --demod_use_ground                      true
% 3.93/1.00  --sup_to_prop_solver                    passive
% 3.93/1.00  --sup_prop_simpl_new                    true
% 3.93/1.00  --sup_prop_simpl_given                  true
% 3.93/1.00  --sup_fun_splitting                     false
% 3.93/1.00  --sup_smt_interval                      50000
% 3.93/1.00  
% 3.93/1.00  ------ Superposition Simplification Setup
% 3.93/1.00  
% 3.93/1.00  --sup_indices_passive                   []
% 3.93/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.93/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/1.00  --sup_full_bw                           [BwDemod]
% 3.93/1.00  --sup_immed_triv                        [TrivRules]
% 3.93/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/1.00  --sup_immed_bw_main                     []
% 3.93/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.93/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.93/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.93/1.00  
% 3.93/1.00  ------ Combination Options
% 3.93/1.00  
% 3.93/1.00  --comb_res_mult                         3
% 3.93/1.00  --comb_sup_mult                         2
% 3.93/1.00  --comb_inst_mult                        10
% 3.93/1.00  
% 3.93/1.00  ------ Debug Options
% 3.93/1.00  
% 3.93/1.00  --dbg_backtrace                         false
% 3.93/1.00  --dbg_dump_prop_clauses                 false
% 3.93/1.00  --dbg_dump_prop_clauses_file            -
% 3.93/1.00  --dbg_out_stat                          false
% 3.93/1.00  ------ Parsing...
% 3.93/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.93/1.00  ------ Proving...
% 3.93/1.00  ------ Problem Properties 
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  clauses                                 32
% 3.93/1.00  conjectures                             15
% 3.93/1.00  EPR                                     11
% 3.93/1.00  Horn                                    25
% 3.93/1.00  unary                                   15
% 3.93/1.00  binary                                  9
% 3.93/1.00  lits                                    68
% 3.93/1.00  lits eq                                 9
% 3.93/1.00  fd_pure                                 0
% 3.93/1.00  fd_pseudo                               0
% 3.93/1.00  fd_cond                                 0
% 3.93/1.00  fd_pseudo_cond                          2
% 3.93/1.00  AC symbols                              0
% 3.93/1.00  
% 3.93/1.00  ------ Input Options Time Limit: Unbounded
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  ------ 
% 3.93/1.00  Current options:
% 3.93/1.00  ------ 
% 3.93/1.00  
% 3.93/1.00  ------ Input Options
% 3.93/1.00  
% 3.93/1.00  --out_options                           all
% 3.93/1.00  --tptp_safe_out                         true
% 3.93/1.00  --problem_path                          ""
% 3.93/1.00  --include_path                          ""
% 3.93/1.00  --clausifier                            res/vclausify_rel
% 3.93/1.00  --clausifier_options                    --mode clausify
% 3.93/1.00  --stdin                                 false
% 3.93/1.00  --stats_out                             sel
% 3.93/1.00  
% 3.93/1.00  ------ General Options
% 3.93/1.00  
% 3.93/1.00  --fof                                   false
% 3.93/1.00  --time_out_real                         604.99
% 3.93/1.00  --time_out_virtual                      -1.
% 3.93/1.00  --symbol_type_check                     false
% 3.93/1.00  --clausify_out                          false
% 3.93/1.00  --sig_cnt_out                           false
% 3.93/1.00  --trig_cnt_out                          false
% 3.93/1.00  --trig_cnt_out_tolerance                1.
% 3.93/1.00  --trig_cnt_out_sk_spl                   false
% 3.93/1.00  --abstr_cl_out                          false
% 3.93/1.00  
% 3.93/1.00  ------ Global Options
% 3.93/1.00  
% 3.93/1.00  --schedule                              none
% 3.93/1.00  --add_important_lit                     false
% 3.93/1.00  --prop_solver_per_cl                    1000
% 3.93/1.00  --min_unsat_core                        false
% 3.93/1.00  --soft_assumptions                      false
% 3.93/1.00  --soft_lemma_size                       3
% 3.93/1.00  --prop_impl_unit_size                   0
% 3.93/1.00  --prop_impl_unit                        []
% 3.93/1.00  --share_sel_clauses                     true
% 3.93/1.00  --reset_solvers                         false
% 3.93/1.00  --bc_imp_inh                            [conj_cone]
% 3.93/1.00  --conj_cone_tolerance                   3.
% 3.93/1.00  --extra_neg_conj                        none
% 3.93/1.00  --large_theory_mode                     true
% 3.93/1.00  --prolific_symb_bound                   200
% 3.93/1.00  --lt_threshold                          2000
% 3.93/1.00  --clause_weak_htbl                      true
% 3.93/1.00  --gc_record_bc_elim                     false
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing Options
% 3.93/1.00  
% 3.93/1.00  --preprocessing_flag                    true
% 3.93/1.00  --time_out_prep_mult                    0.1
% 3.93/1.00  --splitting_mode                        input
% 3.93/1.00  --splitting_grd                         true
% 3.93/1.00  --splitting_cvd                         false
% 3.93/1.00  --splitting_cvd_svl                     false
% 3.93/1.00  --splitting_nvd                         32
% 3.93/1.00  --sub_typing                            true
% 3.93/1.00  --prep_gs_sim                           false
% 3.93/1.00  --prep_unflatten                        true
% 3.93/1.00  --prep_res_sim                          true
% 3.93/1.00  --prep_upred                            true
% 3.93/1.00  --prep_sem_filter                       exhaustive
% 3.93/1.00  --prep_sem_filter_out                   false
% 3.93/1.00  --pred_elim                             false
% 3.93/1.00  --res_sim_input                         true
% 3.93/1.00  --eq_ax_congr_red                       true
% 3.93/1.00  --pure_diseq_elim                       true
% 3.93/1.00  --brand_transform                       false
% 3.93/1.00  --non_eq_to_eq                          false
% 3.93/1.00  --prep_def_merge                        true
% 3.93/1.00  --prep_def_merge_prop_impl              false
% 3.93/1.00  --prep_def_merge_mbd                    true
% 3.93/1.00  --prep_def_merge_tr_red                 false
% 3.93/1.00  --prep_def_merge_tr_cl                  false
% 3.93/1.00  --smt_preprocessing                     true
% 3.93/1.00  --smt_ac_axioms                         fast
% 3.93/1.00  --preprocessed_out                      false
% 3.93/1.00  --preprocessed_stats                    false
% 3.93/1.00  
% 3.93/1.00  ------ Abstraction refinement Options
% 3.93/1.00  
% 3.93/1.00  --abstr_ref                             []
% 3.93/1.00  --abstr_ref_prep                        false
% 3.93/1.00  --abstr_ref_until_sat                   false
% 3.93/1.00  --abstr_ref_sig_restrict                funpre
% 3.93/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.93/1.00  --abstr_ref_under                       []
% 3.93/1.00  
% 3.93/1.00  ------ SAT Options
% 3.93/1.00  
% 3.93/1.00  --sat_mode                              false
% 3.93/1.00  --sat_fm_restart_options                ""
% 3.93/1.00  --sat_gr_def                            false
% 3.93/1.00  --sat_epr_types                         true
% 3.93/1.00  --sat_non_cyclic_types                  false
% 3.93/1.00  --sat_finite_models                     false
% 3.93/1.00  --sat_fm_lemmas                         false
% 3.93/1.00  --sat_fm_prep                           false
% 3.93/1.00  --sat_fm_uc_incr                        true
% 3.93/1.00  --sat_out_model                         small
% 3.93/1.00  --sat_out_clauses                       false
% 3.93/1.00  
% 3.93/1.00  ------ QBF Options
% 3.93/1.00  
% 3.93/1.00  --qbf_mode                              false
% 3.93/1.00  --qbf_elim_univ                         false
% 3.93/1.00  --qbf_dom_inst                          none
% 3.93/1.00  --qbf_dom_pre_inst                      false
% 3.93/1.00  --qbf_sk_in                             false
% 3.93/1.00  --qbf_pred_elim                         true
% 3.93/1.00  --qbf_split                             512
% 3.93/1.00  
% 3.93/1.00  ------ BMC1 Options
% 3.93/1.00  
% 3.93/1.00  --bmc1_incremental                      false
% 3.93/1.00  --bmc1_axioms                           reachable_all
% 3.93/1.00  --bmc1_min_bound                        0
% 3.93/1.00  --bmc1_max_bound                        -1
% 3.93/1.00  --bmc1_max_bound_default                -1
% 3.93/1.00  --bmc1_symbol_reachability              true
% 3.93/1.00  --bmc1_property_lemmas                  false
% 3.93/1.00  --bmc1_k_induction                      false
% 3.93/1.00  --bmc1_non_equiv_states                 false
% 3.93/1.00  --bmc1_deadlock                         false
% 3.93/1.00  --bmc1_ucm                              false
% 3.93/1.00  --bmc1_add_unsat_core                   none
% 3.93/1.00  --bmc1_unsat_core_children              false
% 3.93/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.93/1.00  --bmc1_out_stat                         full
% 3.93/1.00  --bmc1_ground_init                      false
% 3.93/1.00  --bmc1_pre_inst_next_state              false
% 3.93/1.00  --bmc1_pre_inst_state                   false
% 3.93/1.00  --bmc1_pre_inst_reach_state             false
% 3.93/1.00  --bmc1_out_unsat_core                   false
% 3.93/1.00  --bmc1_aig_witness_out                  false
% 3.93/1.00  --bmc1_verbose                          false
% 3.93/1.00  --bmc1_dump_clauses_tptp                false
% 3.93/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.93/1.00  --bmc1_dump_file                        -
% 3.93/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.93/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.93/1.00  --bmc1_ucm_extend_mode                  1
% 3.93/1.00  --bmc1_ucm_init_mode                    2
% 3.93/1.00  --bmc1_ucm_cone_mode                    none
% 3.93/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.93/1.00  --bmc1_ucm_relax_model                  4
% 3.93/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.93/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.93/1.00  --bmc1_ucm_layered_model                none
% 3.93/1.00  --bmc1_ucm_max_lemma_size               10
% 3.93/1.00  
% 3.93/1.00  ------ AIG Options
% 3.93/1.00  
% 3.93/1.00  --aig_mode                              false
% 3.93/1.00  
% 3.93/1.00  ------ Instantiation Options
% 3.93/1.00  
% 3.93/1.00  --instantiation_flag                    true
% 3.93/1.00  --inst_sos_flag                         false
% 3.93/1.00  --inst_sos_phase                        true
% 3.93/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.93/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.93/1.00  --inst_lit_sel_side                     num_symb
% 3.93/1.00  --inst_solver_per_active                1400
% 3.93/1.00  --inst_solver_calls_frac                1.
% 3.93/1.00  --inst_passive_queue_type               priority_queues
% 3.93/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.93/1.00  --inst_passive_queues_freq              [25;2]
% 3.93/1.00  --inst_dismatching                      true
% 3.93/1.00  --inst_eager_unprocessed_to_passive     true
% 3.93/1.00  --inst_prop_sim_given                   true
% 3.93/1.00  --inst_prop_sim_new                     false
% 3.93/1.00  --inst_subs_new                         false
% 3.93/1.00  --inst_eq_res_simp                      false
% 3.93/1.00  --inst_subs_given                       false
% 3.93/1.00  --inst_orphan_elimination               true
% 3.93/1.00  --inst_learning_loop_flag               true
% 3.93/1.00  --inst_learning_start                   3000
% 3.93/1.00  --inst_learning_factor                  2
% 3.93/1.00  --inst_start_prop_sim_after_learn       3
% 3.93/1.00  --inst_sel_renew                        solver
% 3.93/1.00  --inst_lit_activity_flag                true
% 3.93/1.00  --inst_restr_to_given                   false
% 3.93/1.00  --inst_activity_threshold               500
% 3.93/1.00  --inst_out_proof                        true
% 3.93/1.00  
% 3.93/1.00  ------ Resolution Options
% 3.93/1.00  
% 3.93/1.00  --resolution_flag                       true
% 3.93/1.00  --res_lit_sel                           adaptive
% 3.93/1.00  --res_lit_sel_side                      none
% 3.93/1.00  --res_ordering                          kbo
% 3.93/1.00  --res_to_prop_solver                    active
% 3.93/1.00  --res_prop_simpl_new                    false
% 3.93/1.00  --res_prop_simpl_given                  true
% 3.93/1.00  --res_passive_queue_type                priority_queues
% 3.93/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.93/1.00  --res_passive_queues_freq               [15;5]
% 3.93/1.00  --res_forward_subs                      full
% 3.93/1.00  --res_backward_subs                     full
% 3.93/1.00  --res_forward_subs_resolution           true
% 3.93/1.00  --res_backward_subs_resolution          true
% 3.93/1.00  --res_orphan_elimination                true
% 3.93/1.00  --res_time_limit                        2.
% 3.93/1.00  --res_out_proof                         true
% 3.93/1.00  
% 3.93/1.00  ------ Superposition Options
% 3.93/1.00  
% 3.93/1.00  --superposition_flag                    true
% 3.93/1.00  --sup_passive_queue_type                priority_queues
% 3.93/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.93/1.00  --sup_passive_queues_freq               [1;4]
% 3.93/1.00  --demod_completeness_check              fast
% 3.93/1.00  --demod_use_ground                      true
% 3.93/1.00  --sup_to_prop_solver                    passive
% 3.93/1.00  --sup_prop_simpl_new                    true
% 3.93/1.00  --sup_prop_simpl_given                  true
% 3.93/1.00  --sup_fun_splitting                     false
% 3.93/1.00  --sup_smt_interval                      50000
% 3.93/1.00  
% 3.93/1.00  ------ Superposition Simplification Setup
% 3.93/1.00  
% 3.93/1.00  --sup_indices_passive                   []
% 3.93/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.93/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/1.00  --sup_full_bw                           [BwDemod]
% 3.93/1.00  --sup_immed_triv                        [TrivRules]
% 3.93/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/1.00  --sup_immed_bw_main                     []
% 3.93/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.93/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.93/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.93/1.00  
% 3.93/1.00  ------ Combination Options
% 3.93/1.00  
% 3.93/1.00  --comb_res_mult                         3
% 3.93/1.00  --comb_sup_mult                         2
% 3.93/1.00  --comb_inst_mult                        10
% 3.93/1.00  
% 3.93/1.00  ------ Debug Options
% 3.93/1.00  
% 3.93/1.00  --dbg_backtrace                         false
% 3.93/1.00  --dbg_dump_prop_clauses                 false
% 3.93/1.00  --dbg_dump_prop_clauses_file            -
% 3.93/1.00  --dbg_out_stat                          false
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  ------ Proving...
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  % SZS status Theorem for theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  fof(f15,plain,(
% 3.93/1.00    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 3.93/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.93/1.00  
% 3.93/1.00  fof(f21,plain,(
% 3.93/1.00    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X5,X6) & k1_funct_1(X2,X4) = X6 & k1_funct_1(X2,X3) = X5 & m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X2,X0)))),
% 3.93/1.00    inference(nnf_transformation,[],[f15])).
% 3.93/1.00  
% 3.93/1.00  fof(f22,plain,(
% 3.93/1.00    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,X3,X4) & m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X2)))) & (! [X7] : (! [X8] : (! [X9] : (! [X10] : (r1_orders_2(X0,X9,X10) | k1_funct_1(X1,X8) != X10 | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X0))) | ~m1_subset_1(X9,u1_struct_0(X0))) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~sP0(X0,X1,X2)))),
% 3.93/1.00    inference(rectify,[],[f21])).
% 3.93/1.00  
% 3.93/1.00  fof(f26,plain,(
% 3.93/1.00    ( ! [X4,X5,X3] : (! [X2,X1,X0] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) => (~r1_orders_2(X0,X5,sK5(X0,X1,X2)) & k1_funct_1(X1,X4) = sK5(X0,X1,X2) & k1_funct_1(X1,X3) = X5 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))) )),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f25,plain,(
% 3.93/1.00    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) => (? [X6] : (~r1_orders_2(X0,sK4(X0,X1,X2),X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = sK4(X0,X1,X2) & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))) )),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f24,plain,(
% 3.93/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,X3,X4) & m1_subset_1(X4,u1_struct_0(X2))) => (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,sK3(X0,X1,X2)) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,X3,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2))))) )),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f23,plain,(
% 3.93/1.00    ! [X2,X1,X0] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,X3,X4) & m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X2))) => (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,sK2(X0,X1,X2)) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,sK2(X0,X1,X2),X4) & m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2))))),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f27,plain,(
% 3.93/1.00    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((((~r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2)) & k1_funct_1(X1,sK3(X0,X1,X2)) = sK5(X0,X1,X2) & k1_funct_1(X1,sK2(X0,X1,X2)) = sK4(X0,X1,X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) & r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)))) & (! [X7] : (! [X8] : (! [X9] : (! [X10] : (r1_orders_2(X0,X9,X10) | k1_funct_1(X1,X8) != X10 | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X0))) | ~m1_subset_1(X9,u1_struct_0(X0))) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~sP0(X0,X1,X2)))),
% 3.93/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f26,f25,f24,f23])).
% 3.93/1.00  
% 3.93/1.00  fof(f45,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f27])).
% 3.93/1.00  
% 3.93/1.00  fof(f1,axiom,(
% 3.93/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f8,plain,(
% 3.93/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.93/1.00    inference(ennf_transformation,[],[f1])).
% 3.93/1.00  
% 3.93/1.00  fof(f18,plain,(
% 3.93/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.93/1.00    inference(nnf_transformation,[],[f8])).
% 3.93/1.00  
% 3.93/1.00  fof(f35,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f18])).
% 3.93/1.00  
% 3.93/1.00  fof(f5,conjecture,(
% 3.93/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((l1_orders_2(X2) & ~v2_struct_0(X2)) => ! [X3] : ((l1_orders_2(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f6,negated_conjecture,(
% 3.93/1.00    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((l1_orders_2(X2) & ~v2_struct_0(X2)) => ! [X3] : ((l1_orders_2(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 3.93/1.00    inference(negated_conjecture,[],[f5])).
% 3.93/1.00  
% 3.93/1.00  fof(f7,plain,(
% 3.93/1.00    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : (l1_orders_2(X2) => ! [X3] : (l1_orders_2(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 3.93/1.00    inference(pure_predicate_removal,[],[f6])).
% 3.93/1.00  
% 3.93/1.00  fof(f13,plain,(
% 3.93/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~v5_orders_3(X5,X2,X3) & (v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 3.93/1.00    inference(ennf_transformation,[],[f7])).
% 3.93/1.00  
% 3.93/1.00  fof(f14,plain,(
% 3.93/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 3.93/1.00    inference(flattening,[],[f13])).
% 3.93/1.00  
% 3.93/1.00  fof(f33,plain,(
% 3.93/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => (~v5_orders_3(sK11,X2,X3) & v5_orders_3(X4,X0,X1) & sK11 = X4 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(sK11,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(sK11))) )),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f32,plain,(
% 3.93/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(sK10,X0,X1) & sK10 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK10,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK10))) )),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f31,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) => (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,sK9) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK9)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK9)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(sK9))) )),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f30,plain,(
% 3.93/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) => (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,sK8,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(sK8),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(sK8))) )),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f29,plain,(
% 3.93/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,sK7) & X4 = X5 & g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK7)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(sK7))) )),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f28,plain,(
% 3.93/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,sK6,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(sK6))),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f34,plain,(
% 3.93/1.00    (((((~v5_orders_3(sK11,sK8,sK9) & v5_orders_3(sK10,sK6,sK7) & sK10 = sK11 & g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) & g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) & v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) & v1_funct_1(sK11)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(sK10)) & l1_orders_2(sK9)) & l1_orders_2(sK8)) & l1_orders_2(sK7)) & l1_orders_2(sK6)),
% 3.93/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f14,f33,f32,f31,f30,f29,f28])).
% 3.93/1.00  
% 3.93/1.00  fof(f62,plain,(
% 3.93/1.00    g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8))),
% 3.93/1.00    inference(cnf_transformation,[],[f34])).
% 3.93/1.00  
% 3.93/1.00  fof(f3,axiom,(
% 3.93/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f10,plain,(
% 3.93/1.00    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.93/1.00    inference(ennf_transformation,[],[f3])).
% 3.93/1.00  
% 3.93/1.00  fof(f39,plain,(
% 3.93/1.00    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f10])).
% 3.93/1.00  
% 3.93/1.00  fof(f52,plain,(
% 3.93/1.00    l1_orders_2(sK6)),
% 3.93/1.00    inference(cnf_transformation,[],[f34])).
% 3.93/1.00  
% 3.93/1.00  fof(f2,axiom,(
% 3.93/1.00    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f9,plain,(
% 3.93/1.00    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.93/1.00    inference(ennf_transformation,[],[f2])).
% 3.93/1.00  
% 3.93/1.00  fof(f37,plain,(
% 3.93/1.00    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f9])).
% 3.93/1.00  
% 3.93/1.00  fof(f36,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f18])).
% 3.93/1.00  
% 3.93/1.00  fof(f38,plain,(
% 3.93/1.00    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f10])).
% 3.93/1.00  
% 3.93/1.00  fof(f54,plain,(
% 3.93/1.00    l1_orders_2(sK8)),
% 3.93/1.00    inference(cnf_transformation,[],[f34])).
% 3.93/1.00  
% 3.93/1.00  fof(f44,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f27])).
% 3.93/1.00  
% 3.93/1.00  fof(f43,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f27])).
% 3.93/1.00  
% 3.93/1.00  fof(f48,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | k1_funct_1(X1,sK2(X0,X1,X2)) = sK4(X0,X1,X2)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f27])).
% 3.93/1.00  
% 3.93/1.00  fof(f61,plain,(
% 3.93/1.00    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))),
% 3.93/1.00    inference(cnf_transformation,[],[f34])).
% 3.93/1.00  
% 3.93/1.00  fof(f4,axiom,(
% 3.93/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_orders_3(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_orders_2(X0,X3,X4) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X1)) => ((k1_funct_1(X2,X4) = X6 & k1_funct_1(X2,X3) = X5) => r1_orders_2(X1,X5,X6)))))))))))),
% 3.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f11,plain,(
% 3.93/1.00    ! [X0] : (! [X1] : (! [X2] : ((v5_orders_3(X2,X0,X1) <=> ! [X3] : (! [X4] : ((! [X5] : (! [X6] : ((r1_orders_2(X1,X5,X6) | (k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5)) | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 3.93/1.00    inference(ennf_transformation,[],[f4])).
% 3.93/1.00  
% 3.93/1.00  fof(f12,plain,(
% 3.93/1.00    ! [X0] : (! [X1] : (! [X2] : ((v5_orders_3(X2,X0,X1) <=> ! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 3.93/1.00    inference(flattening,[],[f11])).
% 3.93/1.00  
% 3.93/1.00  fof(f16,plain,(
% 3.93/1.00    ! [X0,X2,X1] : ((v5_orders_3(X2,X0,X1) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 3.93/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.93/1.00  
% 3.93/1.00  fof(f17,plain,(
% 3.93/1.00    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 3.93/1.00    inference(definition_folding,[],[f12,f16,f15])).
% 3.93/1.00  
% 3.93/1.00  fof(f51,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f17])).
% 3.93/1.00  
% 3.93/1.00  fof(f55,plain,(
% 3.93/1.00    l1_orders_2(sK9)),
% 3.93/1.00    inference(cnf_transformation,[],[f34])).
% 3.93/1.00  
% 3.93/1.00  fof(f59,plain,(
% 3.93/1.00    v1_funct_1(sK11)),
% 3.93/1.00    inference(cnf_transformation,[],[f34])).
% 3.93/1.00  
% 3.93/1.00  fof(f60,plain,(
% 3.93/1.00    v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9))),
% 3.93/1.00    inference(cnf_transformation,[],[f34])).
% 3.93/1.00  
% 3.93/1.00  fof(f19,plain,(
% 3.93/1.00    ! [X0,X2,X1] : (((v5_orders_3(X2,X0,X1) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~v5_orders_3(X2,X0,X1))) | ~sP1(X0,X2,X1))),
% 3.93/1.00    inference(nnf_transformation,[],[f16])).
% 3.93/1.00  
% 3.93/1.00  fof(f20,plain,(
% 3.93/1.00    ! [X0,X1,X2] : (((v5_orders_3(X1,X0,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v5_orders_3(X1,X0,X2))) | ~sP1(X0,X1,X2))),
% 3.93/1.00    inference(rectify,[],[f19])).
% 3.93/1.00  
% 3.93/1.00  fof(f41,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (v5_orders_3(X1,X0,X2) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f20])).
% 3.93/1.00  
% 3.93/1.00  fof(f66,plain,(
% 3.93/1.00    ~v5_orders_3(sK11,sK8,sK9)),
% 3.93/1.00    inference(cnf_transformation,[],[f34])).
% 3.93/1.00  
% 3.93/1.00  fof(f49,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | k1_funct_1(X1,sK3(X0,X1,X2)) = sK5(X0,X1,X2)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f27])).
% 3.93/1.00  
% 3.93/1.00  fof(f58,plain,(
% 3.93/1.00    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))),
% 3.93/1.00    inference(cnf_transformation,[],[f34])).
% 3.93/1.00  
% 3.93/1.00  fof(f64,plain,(
% 3.93/1.00    sK10 = sK11),
% 3.93/1.00    inference(cnf_transformation,[],[f34])).
% 3.93/1.00  
% 3.93/1.00  fof(f53,plain,(
% 3.93/1.00    l1_orders_2(sK7)),
% 3.93/1.00    inference(cnf_transformation,[],[f34])).
% 3.93/1.00  
% 3.93/1.00  fof(f57,plain,(
% 3.93/1.00    v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7))),
% 3.93/1.00    inference(cnf_transformation,[],[f34])).
% 3.93/1.00  
% 3.93/1.00  fof(f40,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | ~v5_orders_3(X1,X0,X2) | ~sP1(X0,X1,X2)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f20])).
% 3.93/1.00  
% 3.93/1.00  fof(f65,plain,(
% 3.93/1.00    v5_orders_3(sK10,sK6,sK7)),
% 3.93/1.00    inference(cnf_transformation,[],[f34])).
% 3.93/1.00  
% 3.93/1.00  fof(f42,plain,(
% 3.93/1.00    ( ! [X2,X0,X10,X8,X7,X1,X9] : (r1_orders_2(X0,X9,X10) | k1_funct_1(X1,X8) != X10 | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X0)) | ~m1_subset_1(X9,u1_struct_0(X0)) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f27])).
% 3.93/1.00  
% 3.93/1.00  fof(f67,plain,(
% 3.93/1.00    ( ! [X2,X0,X8,X7,X1,X9] : (r1_orders_2(X0,X9,k1_funct_1(X1,X8)) | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0)) | ~m1_subset_1(X9,u1_struct_0(X0)) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 3.93/1.00    inference(equality_resolution,[],[f42])).
% 3.93/1.00  
% 3.93/1.00  fof(f68,plain,(
% 3.93/1.00    ( ! [X2,X0,X8,X7,X1] : (r1_orders_2(X0,k1_funct_1(X1,X7),k1_funct_1(X1,X8)) | ~m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0)) | ~m1_subset_1(k1_funct_1(X1,X7),u1_struct_0(X0)) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 3.93/1.00    inference(equality_resolution,[],[f67])).
% 3.93/1.00  
% 3.93/1.00  fof(f63,plain,(
% 3.93/1.00    g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9))),
% 3.93/1.00    inference(cnf_transformation,[],[f34])).
% 3.93/1.00  
% 3.93/1.00  fof(f47,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f27])).
% 3.93/1.00  
% 3.93/1.00  fof(f46,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f27])).
% 3.93/1.00  
% 3.93/1.00  fof(f50,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f27])).
% 3.93/1.00  
% 3.93/1.00  cnf(c_12,plain,
% 3.93/1.00      ( sP0(X0,X1,X2) | r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2)) ),
% 3.93/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_789,plain,
% 3.93/1.00      ( sP0(X0,X1,X2) = iProver_top
% 3.93/1.00      | r1_orders_2(X2,sK2(X0,X1,X2),sK3(X0,X1,X2)) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1,plain,
% 3.93/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.93/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.93/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.93/1.00      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 3.93/1.00      | ~ l1_orders_2(X0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_800,plain,
% 3.93/1.00      ( r1_orders_2(X0,X1,X2) != iProver_top
% 3.93/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.93/1.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.93/1.00      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) = iProver_top
% 3.93/1.00      | l1_orders_2(X0) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_21,negated_conjecture,
% 3.93/1.00      ( g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) ),
% 3.93/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3,plain,
% 3.93/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.93/1.00      | X2 = X0
% 3.93/1.00      | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_798,plain,
% 3.93/1.00      ( X0 = X1
% 3.93/1.00      | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
% 3.93/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2416,plain,
% 3.93/1.00      ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
% 3.93/1.00      | u1_orders_2(sK6) = X1
% 3.93/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_21,c_798]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_31,negated_conjecture,
% 3.93/1.00      ( l1_orders_2(sK6) ),
% 3.93/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2,plain,
% 3.93/1.00      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.93/1.00      | ~ l1_orders_2(X0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_85,plain,
% 3.93/1.00      ( m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
% 3.93/1.00      | ~ l1_orders_2(sK6) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2418,plain,
% 3.93/1.00      ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
% 3.93/1.00      | u1_orders_2(sK6) = X1
% 3.93/1.00      | m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_21,c_798]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2453,plain,
% 3.93/1.00      ( ~ m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
% 3.93/1.00      | g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
% 3.93/1.00      | u1_orders_2(sK6) = X1 ),
% 3.93/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2418]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2789,plain,
% 3.93/1.00      ( u1_orders_2(sK6) = X1
% 3.93/1.00      | g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1) ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_2416,c_31,c_85,c_2453]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2790,plain,
% 3.93/1.00      ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
% 3.93/1.00      | u1_orders_2(sK6) = X1 ),
% 3.93/1.00      inference(renaming,[status(thm)],[c_2789]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2796,plain,
% 3.93/1.00      ( u1_orders_2(sK8) = u1_orders_2(sK6) ),
% 3.93/1.00      inference(equality_resolution,[status(thm)],[c_2790]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_0,plain,
% 3.93/1.00      ( r1_orders_2(X0,X1,X2)
% 3.93/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.93/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.93/1.00      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 3.93/1.00      | ~ l1_orders_2(X0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_801,plain,
% 3.93/1.00      ( r1_orders_2(X0,X1,X2) = iProver_top
% 3.93/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.93/1.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.93/1.00      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) != iProver_top
% 3.93/1.00      | l1_orders_2(X0) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_5739,plain,
% 3.93/1.00      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.93/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.93/1.00      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK8)) != iProver_top
% 3.93/1.00      | l1_orders_2(sK6) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_2796,c_801]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_4,plain,
% 3.93/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.93/1.00      | X2 = X1
% 3.93/1.00      | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_797,plain,
% 3.93/1.00      ( X0 = X1
% 3.93/1.00      | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
% 3.93/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2308,plain,
% 3.93/1.00      ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
% 3.93/1.00      | u1_struct_0(sK6) = X0
% 3.93/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_21,c_797]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_32,plain,
% 3.93/1.00      ( l1_orders_2(sK6) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_84,plain,
% 3.93/1.00      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
% 3.93/1.00      | l1_orders_2(X0) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_86,plain,
% 3.93/1.00      ( m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) = iProver_top
% 3.93/1.00      | l1_orders_2(sK6) != iProver_top ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_84]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2310,plain,
% 3.93/1.00      ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
% 3.93/1.00      | u1_struct_0(sK6) = X0
% 3.93/1.00      | m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_21,c_797]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2562,plain,
% 3.93/1.00      ( u1_struct_0(sK6) = X0
% 3.93/1.00      | g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1) ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_2308,c_32,c_86,c_2310]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2563,plain,
% 3.93/1.00      ( g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(X0,X1)
% 3.93/1.00      | u1_struct_0(sK6) = X0 ),
% 3.93/1.00      inference(renaming,[status(thm)],[c_2562]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2569,plain,
% 3.93/1.00      ( u1_struct_0(sK8) = u1_struct_0(sK6) ),
% 3.93/1.00      inference(equality_resolution,[status(thm)],[c_2563]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_5761,plain,
% 3.93/1.00      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK8)) != iProver_top
% 3.93/1.00      | l1_orders_2(sK6) != iProver_top ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_5739,c_2569]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_11045,plain,
% 3.93/1.00      ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | r1_orders_2(sK6,X0,X1) = iProver_top ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_5761,c_32]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_11046,plain,
% 3.93/1.00      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK8)) != iProver_top ),
% 3.93/1.00      inference(renaming,[status(thm)],[c_11045]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_11055,plain,
% 3.93/1.00      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.93/1.00      | r1_orders_2(sK8,X0,X1) != iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | l1_orders_2(sK8) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_800,c_11046]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_29,negated_conjecture,
% 3.93/1.00      ( l1_orders_2(sK8) ),
% 3.93/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_34,plain,
% 3.93/1.00      ( l1_orders_2(sK8) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_11320,plain,
% 3.93/1.00      ( m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | r1_orders_2(sK8,X0,X1) != iProver_top
% 3.93/1.00      | r1_orders_2(sK6,X0,X1) = iProver_top ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_11055,c_34]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_11321,plain,
% 3.93/1.00      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.93/1.00      | r1_orders_2(sK8,X0,X1) != iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top ),
% 3.93/1.00      inference(renaming,[status(thm)],[c_11320]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_11330,plain,
% 3.93/1.00      ( sP0(X0,X1,sK8) = iProver_top
% 3.93/1.00      | r1_orders_2(sK6,sK2(X0,X1,sK8),sK3(X0,X1,sK8)) = iProver_top
% 3.93/1.00      | m1_subset_1(sK2(X0,X1,sK8),u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(sK3(X0,X1,sK8),u1_struct_0(sK8)) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_789,c_11321]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_13,plain,
% 3.93/1.00      ( sP0(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2)) ),
% 3.93/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_788,plain,
% 3.93/1.00      ( sP0(X0,X1,X2) = iProver_top
% 3.93/1.00      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X2)) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_14,plain,
% 3.93/1.00      ( sP0(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) ),
% 3.93/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_787,plain,
% 3.93/1.00      ( sP0(X0,X1,X2) = iProver_top
% 3.93/1.00      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X2)) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_11375,plain,
% 3.93/1.00      ( sP0(X0,X1,sK8) = iProver_top
% 3.93/1.00      | r1_orders_2(sK6,sK2(X0,X1,sK8),sK3(X0,X1,sK8)) = iProver_top ),
% 3.93/1.00      inference(forward_subsumption_resolution,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_11330,c_788,c_787]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_9,plain,
% 3.93/1.00      ( sP0(X0,X1,X2) | k1_funct_1(X1,sK2(X0,X1,X2)) = sK4(X0,X1,X2) ),
% 3.93/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_792,plain,
% 3.93/1.00      ( k1_funct_1(X0,sK2(X1,X0,X2)) = sK4(X1,X0,X2)
% 3.93/1.00      | sP0(X1,X0,X2) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_22,negated_conjecture,
% 3.93/1.00      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) ),
% 3.93/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_782,plain,
% 3.93/1.00      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_16,plain,
% 3.93/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.93/1.00      | sP1(X1,X0,X2)
% 3.93/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.93/1.00      | ~ v1_funct_1(X0)
% 3.93/1.00      | ~ l1_orders_2(X1)
% 3.93/1.00      | ~ l1_orders_2(X2) ),
% 3.93/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_785,plain,
% 3.93/1.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.93/1.00      | sP1(X1,X0,X2) = iProver_top
% 3.93/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.93/1.00      | v1_funct_1(X0) != iProver_top
% 3.93/1.00      | l1_orders_2(X1) != iProver_top
% 3.93/1.00      | l1_orders_2(X2) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1579,plain,
% 3.93/1.00      ( v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) != iProver_top
% 3.93/1.00      | sP1(sK8,sK11,sK9) = iProver_top
% 3.93/1.00      | v1_funct_1(sK11) != iProver_top
% 3.93/1.00      | l1_orders_2(sK9) != iProver_top
% 3.93/1.00      | l1_orders_2(sK8) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_782,c_785]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_28,negated_conjecture,
% 3.93/1.00      ( l1_orders_2(sK9) ),
% 3.93/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_35,plain,
% 3.93/1.00      ( l1_orders_2(sK9) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_24,negated_conjecture,
% 3.93/1.00      ( v1_funct_1(sK11) ),
% 3.93/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_39,plain,
% 3.93/1.00      ( v1_funct_1(sK11) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_23,negated_conjecture,
% 3.93/1.00      ( v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) ),
% 3.93/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_40,plain,
% 3.93/1.00      ( v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_41,plain,
% 3.93/1.00      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1096,plain,
% 3.93/1.00      ( ~ v1_funct_2(sK11,u1_struct_0(X0),u1_struct_0(X1))
% 3.93/1.00      | sP1(X0,sK11,X1)
% 3.93/1.00      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.93/1.00      | ~ v1_funct_1(sK11)
% 3.93/1.00      | ~ l1_orders_2(X0)
% 3.93/1.00      | ~ l1_orders_2(X1) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1226,plain,
% 3.93/1.00      ( ~ v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9))
% 3.93/1.00      | sP1(sK8,sK11,sK9)
% 3.93/1.00      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
% 3.93/1.00      | ~ v1_funct_1(sK11)
% 3.93/1.00      | ~ l1_orders_2(sK9)
% 3.93/1.00      | ~ l1_orders_2(sK8) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_1096]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1227,plain,
% 3.93/1.00      ( v1_funct_2(sK11,u1_struct_0(sK8),u1_struct_0(sK9)) != iProver_top
% 3.93/1.00      | sP1(sK8,sK11,sK9) = iProver_top
% 3.93/1.00      | m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) != iProver_top
% 3.93/1.00      | v1_funct_1(sK11) != iProver_top
% 3.93/1.00      | l1_orders_2(sK9) != iProver_top
% 3.93/1.00      | l1_orders_2(sK8) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1226]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3098,plain,
% 3.93/1.00      ( sP1(sK8,sK11,sK9) = iProver_top ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_1579,c_34,c_35,c_39,c_40,c_41,c_1227]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_5,plain,
% 3.93/1.00      ( ~ sP1(X0,X1,X2) | ~ sP0(X2,X1,X0) | v5_orders_3(X1,X0,X2) ),
% 3.93/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_796,plain,
% 3.93/1.00      ( sP1(X0,X1,X2) != iProver_top
% 3.93/1.00      | sP0(X2,X1,X0) != iProver_top
% 3.93/1.00      | v5_orders_3(X1,X0,X2) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3103,plain,
% 3.93/1.00      ( sP0(sK9,sK11,sK8) != iProver_top
% 3.93/1.00      | v5_orders_3(sK11,sK8,sK9) = iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_3098,c_796]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_17,negated_conjecture,
% 3.93/1.00      ( ~ v5_orders_3(sK11,sK8,sK9) ),
% 3.93/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_43,plain,
% 3.93/1.00      ( v5_orders_3(sK11,sK8,sK9) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1254,plain,
% 3.93/1.00      ( ~ sP1(sK8,sK11,sK9)
% 3.93/1.00      | ~ sP0(sK9,sK11,sK8)
% 3.93/1.00      | v5_orders_3(sK11,sK8,sK9) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1255,plain,
% 3.93/1.00      ( sP1(sK8,sK11,sK9) != iProver_top
% 3.93/1.00      | sP0(sK9,sK11,sK8) != iProver_top
% 3.93/1.00      | v5_orders_3(sK11,sK8,sK9) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1254]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3246,plain,
% 3.93/1.00      ( sP0(sK9,sK11,sK8) != iProver_top ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_3103,c_34,c_35,c_39,c_40,c_41,c_43,c_1227,c_1255]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3252,plain,
% 3.93/1.00      ( k1_funct_1(sK11,sK2(sK9,sK11,sK8)) = sK4(sK9,sK11,sK8) ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_792,c_3246]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_8,plain,
% 3.93/1.00      ( sP0(X0,X1,X2) | k1_funct_1(X1,sK3(X0,X1,X2)) = sK5(X0,X1,X2) ),
% 3.93/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_793,plain,
% 3.93/1.00      ( k1_funct_1(X0,sK3(X1,X0,X2)) = sK5(X1,X0,X2)
% 3.93/1.00      | sP0(X1,X0,X2) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3251,plain,
% 3.93/1.00      ( k1_funct_1(sK11,sK3(sK9,sK11,sK8)) = sK5(sK9,sK11,sK8) ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_793,c_3246]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_25,negated_conjecture,
% 3.93/1.00      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
% 3.93/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_779,plain,
% 3.93/1.00      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_19,negated_conjecture,
% 3.93/1.00      ( sK10 = sK11 ),
% 3.93/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_825,plain,
% 3.93/1.00      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_779,c_19]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1580,plain,
% 3.93/1.00      ( v1_funct_2(sK11,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 3.93/1.00      | sP1(sK6,sK11,sK7) = iProver_top
% 3.93/1.00      | v1_funct_1(sK11) != iProver_top
% 3.93/1.00      | l1_orders_2(sK7) != iProver_top
% 3.93/1.00      | l1_orders_2(sK6) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_825,c_785]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_30,negated_conjecture,
% 3.93/1.00      ( l1_orders_2(sK7) ),
% 3.93/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_33,plain,
% 3.93/1.00      ( l1_orders_2(sK7) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_26,negated_conjecture,
% 3.93/1.00      ( v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7)) ),
% 3.93/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_778,plain,
% 3.93/1.00      ( v1_funct_2(sK10,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_820,plain,
% 3.93/1.00      ( v1_funct_2(sK11,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_778,c_19]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3258,plain,
% 3.93/1.00      ( sP1(sK6,sK11,sK7) = iProver_top ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_1580,c_32,c_33,c_39,c_820]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_6,plain,
% 3.93/1.00      ( ~ sP1(X0,X1,X2) | sP0(X2,X1,X0) | ~ v5_orders_3(X1,X0,X2) ),
% 3.93/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_795,plain,
% 3.93/1.00      ( sP1(X0,X1,X2) != iProver_top
% 3.93/1.00      | sP0(X2,X1,X0) = iProver_top
% 3.93/1.00      | v5_orders_3(X1,X0,X2) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3264,plain,
% 3.93/1.00      ( sP0(sK7,sK11,sK6) = iProver_top
% 3.93/1.00      | v5_orders_3(sK11,sK6,sK7) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_3258,c_795]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_18,negated_conjecture,
% 3.93/1.00      ( v5_orders_3(sK10,sK6,sK7) ),
% 3.93/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_783,plain,
% 3.93/1.00      ( v5_orders_3(sK10,sK6,sK7) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_815,plain,
% 3.93/1.00      ( v5_orders_3(sK11,sK6,sK7) = iProver_top ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_783,c_19]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3513,plain,
% 3.93/1.00      ( sP0(sK7,sK11,sK6) = iProver_top ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_3264,c_815]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_15,plain,
% 3.93/1.00      ( ~ sP0(X0,X1,X2)
% 3.93/1.00      | ~ r1_orders_2(X2,X3,X4)
% 3.93/1.00      | r1_orders_2(X0,k1_funct_1(X1,X3),k1_funct_1(X1,X4))
% 3.93/1.00      | ~ m1_subset_1(X4,u1_struct_0(X2))
% 3.93/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.93/1.00      | ~ m1_subset_1(k1_funct_1(X1,X4),u1_struct_0(X0))
% 3.93/1.00      | ~ m1_subset_1(k1_funct_1(X1,X3),u1_struct_0(X0)) ),
% 3.93/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_786,plain,
% 3.93/1.00      ( sP0(X0,X1,X2) != iProver_top
% 3.93/1.00      | r1_orders_2(X2,X3,X4) != iProver_top
% 3.93/1.00      | r1_orders_2(X0,k1_funct_1(X1,X3),k1_funct_1(X1,X4)) = iProver_top
% 3.93/1.00      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 3.93/1.00      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 3.93/1.00      | m1_subset_1(k1_funct_1(X1,X4),u1_struct_0(X0)) != iProver_top
% 3.93/1.00      | m1_subset_1(k1_funct_1(X1,X3),u1_struct_0(X0)) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3518,plain,
% 3.93/1.00      ( r1_orders_2(sK7,k1_funct_1(sK11,X0),k1_funct_1(sK11,X1)) = iProver_top
% 3.93/1.00      | r1_orders_2(sK6,X0,X1) != iProver_top
% 3.93/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.93/1.00      | m1_subset_1(k1_funct_1(sK11,X1),u1_struct_0(sK7)) != iProver_top
% 3.93/1.00      | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK7)) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_3513,c_786]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_20,negated_conjecture,
% 3.93/1.00      ( g1_orders_2(u1_struct_0(sK7),u1_orders_2(sK7)) = g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) ),
% 3.93/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2307,plain,
% 3.93/1.00      ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(X0,X1)
% 3.93/1.00      | u1_struct_0(sK7) = X0
% 3.93/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_20,c_797]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2462,plain,
% 3.93/1.00      ( u1_struct_0(sK9) = u1_struct_0(sK7)
% 3.93/1.00      | m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)))) != iProver_top ),
% 3.93/1.00      inference(equality_resolution,[status(thm)],[c_2307]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2474,plain,
% 3.93/1.00      ( ~ m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
% 3.93/1.00      | u1_struct_0(sK9) = u1_struct_0(sK7) ),
% 3.93/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2462]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2914,plain,
% 3.93/1.00      ( m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
% 3.93/1.00      | ~ l1_orders_2(sK9) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3523,plain,
% 3.93/1.00      ( u1_struct_0(sK9) = u1_struct_0(sK7) ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_2462,c_28,c_2474,c_2914]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_6287,plain,
% 3.93/1.00      ( r1_orders_2(sK7,k1_funct_1(sK11,X0),k1_funct_1(sK11,X1)) = iProver_top
% 3.93/1.00      | r1_orders_2(sK6,X0,X1) != iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK9)) != iProver_top
% 3.93/1.00      | m1_subset_1(k1_funct_1(sK11,X1),u1_struct_0(sK9)) != iProver_top ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_3518,c_2569,c_3523]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_6300,plain,
% 3.93/1.00      ( r1_orders_2(sK7,k1_funct_1(sK11,X0),sK5(sK9,sK11,sK8)) = iProver_top
% 3.93/1.00      | r1_orders_2(sK6,X0,sK3(sK9,sK11,sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(sK3(sK9,sK11,sK8),u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK9)) != iProver_top
% 3.93/1.00      | m1_subset_1(k1_funct_1(sK11,sK3(sK9,sK11,sK8)),u1_struct_0(sK9)) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_3251,c_6287]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_6351,plain,
% 3.93/1.00      ( r1_orders_2(sK7,k1_funct_1(sK11,X0),sK5(sK9,sK11,sK8)) = iProver_top
% 3.93/1.00      | r1_orders_2(sK6,X0,sK3(sK9,sK11,sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(sK3(sK9,sK11,sK8),u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top
% 3.93/1.00      | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK9)) != iProver_top ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_6300,c_3251]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_10,plain,
% 3.93/1.00      ( sP0(X0,X1,X2) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ),
% 3.93/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1394,plain,
% 3.93/1.00      ( sP0(sK9,sK11,sK8)
% 3.93/1.00      | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1395,plain,
% 3.93/1.00      ( sP0(sK9,sK11,sK8) = iProver_top
% 3.93/1.00      | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1394]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1392,plain,
% 3.93/1.00      ( sP0(sK9,sK11,sK8)
% 3.93/1.00      | m1_subset_1(sK3(sK9,sK11,sK8),u1_struct_0(sK8)) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1399,plain,
% 3.93/1.00      ( sP0(sK9,sK11,sK8) = iProver_top
% 3.93/1.00      | m1_subset_1(sK3(sK9,sK11,sK8),u1_struct_0(sK8)) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1392]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_13741,plain,
% 3.93/1.00      ( r1_orders_2(sK7,k1_funct_1(sK11,X0),sK5(sK9,sK11,sK8)) = iProver_top
% 3.93/1.00      | r1_orders_2(sK6,X0,sK3(sK9,sK11,sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(k1_funct_1(sK11,X0),u1_struct_0(sK9)) != iProver_top ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_6351,c_34,c_35,c_39,c_40,c_41,c_43,c_1227,c_1255,
% 3.93/1.00                 c_1395,c_1399]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_13751,plain,
% 3.93/1.00      ( r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
% 3.93/1.00      | r1_orders_2(sK6,sK2(sK9,sK11,sK8),sK3(sK9,sK11,sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(sK2(sK9,sK11,sK8),u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(k1_funct_1(sK11,sK2(sK9,sK11,sK8)),u1_struct_0(sK9)) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_3252,c_13741]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_13804,plain,
% 3.93/1.00      ( r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
% 3.93/1.00      | r1_orders_2(sK6,sK2(sK9,sK11,sK8),sK3(sK9,sK11,sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(sK2(sK9,sK11,sK8),u1_struct_0(sK8)) != iProver_top
% 3.93/1.00      | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_13751,c_3252]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_11,plain,
% 3.93/1.00      ( sP0(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ),
% 3.93/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1393,plain,
% 3.93/1.00      ( sP0(sK9,sK11,sK8)
% 3.93/1.00      | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1397,plain,
% 3.93/1.00      ( sP0(sK9,sK11,sK8) = iProver_top
% 3.93/1.00      | m1_subset_1(sK4(sK9,sK11,sK8),u1_struct_0(sK9)) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1393]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1391,plain,
% 3.93/1.00      ( sP0(sK9,sK11,sK8)
% 3.93/1.00      | m1_subset_1(sK2(sK9,sK11,sK8),u1_struct_0(sK8)) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1401,plain,
% 3.93/1.00      ( sP0(sK9,sK11,sK8) = iProver_top
% 3.93/1.00      | m1_subset_1(sK2(sK9,sK11,sK8),u1_struct_0(sK8)) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1391]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_13992,plain,
% 3.93/1.00      ( r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
% 3.93/1.00      | r1_orders_2(sK6,sK2(sK9,sK11,sK8),sK3(sK9,sK11,sK8)) != iProver_top ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_13804,c_34,c_35,c_39,c_40,c_41,c_43,c_1227,c_1255,
% 3.93/1.00                 c_1397,c_1401]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_13998,plain,
% 3.93/1.00      ( sP0(sK9,sK11,sK8) = iProver_top
% 3.93/1.00      | r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_11375,c_13992]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_14254,plain,
% 3.93/1.00      ( r1_orders_2(sK7,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_13998,c_34,c_35,c_39,c_40,c_41,c_43,c_1227,c_1255]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_790,plain,
% 3.93/1.00      ( sP0(X0,X1,X2) = iProver_top
% 3.93/1.00      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2415,plain,
% 3.93/1.00      ( g1_orders_2(u1_struct_0(sK9),u1_orders_2(sK9)) != g1_orders_2(X0,X1)
% 3.93/1.00      | u1_orders_2(sK7) = X1
% 3.93/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_20,c_798]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2646,plain,
% 3.93/1.00      ( u1_orders_2(sK9) = u1_orders_2(sK7)
% 3.93/1.00      | m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)))) != iProver_top ),
% 3.93/1.00      inference(equality_resolution,[status(thm)],[c_2415]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2662,plain,
% 3.93/1.00      ( ~ m1_subset_1(u1_orders_2(sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9))))
% 3.93/1.00      | u1_orders_2(sK9) = u1_orders_2(sK7) ),
% 3.93/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2646]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_4629,plain,
% 3.93/1.00      ( u1_orders_2(sK9) = u1_orders_2(sK7) ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_2646,c_28,c_2662,c_2914]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_4648,plain,
% 3.93/1.00      ( r1_orders_2(sK7,X0,X1) != iProver_top
% 3.93/1.00      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 3.93/1.00      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK9)) = iProver_top
% 3.93/1.00      | l1_orders_2(sK7) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_4629,c_800]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_4658,plain,
% 3.93/1.00      ( r1_orders_2(sK7,X0,X1) != iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 3.93/1.00      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 3.93/1.00      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK9)) = iProver_top
% 3.93/1.00      | l1_orders_2(sK7) != iProver_top ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_4648,c_3523]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_8031,plain,
% 3.93/1.00      ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK9)) = iProver_top
% 3.93/1.00      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 3.93/1.00      | r1_orders_2(sK7,X0,X1) != iProver_top ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_4658,c_33]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_8032,plain,
% 3.93/1.00      ( r1_orders_2(sK7,X0,X1) != iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 3.93/1.00      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 3.93/1.00      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK9)) = iProver_top ),
% 3.93/1.00      inference(renaming,[status(thm)],[c_8031]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_8041,plain,
% 3.93/1.00      ( r1_orders_2(sK7,X0,X1) != iProver_top
% 3.93/1.00      | r1_orders_2(sK9,X0,X1) = iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 3.93/1.00      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 3.93/1.00      | l1_orders_2(sK9) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_8032,c_801]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_8214,plain,
% 3.93/1.00      ( m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 3.93/1.00      | r1_orders_2(sK9,X0,X1) = iProver_top
% 3.93/1.00      | r1_orders_2(sK7,X0,X1) != iProver_top ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_8041,c_35]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_8215,plain,
% 3.93/1.00      ( r1_orders_2(sK7,X0,X1) != iProver_top
% 3.93/1.00      | r1_orders_2(sK9,X0,X1) = iProver_top
% 3.93/1.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 3.93/1.00      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
% 3.93/1.00      inference(renaming,[status(thm)],[c_8214]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_8225,plain,
% 3.93/1.00      ( sP0(sK9,X0,X1) = iProver_top
% 3.93/1.00      | r1_orders_2(sK7,sK4(sK9,X0,X1),X2) != iProver_top
% 3.93/1.00      | r1_orders_2(sK9,sK4(sK9,X0,X1),X2) = iProver_top
% 3.93/1.00      | m1_subset_1(X2,u1_struct_0(sK9)) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_790,c_8215]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_14261,plain,
% 3.93/1.00      ( sP0(sK9,sK11,sK8) = iProver_top
% 3.93/1.00      | r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) = iProver_top
% 3.93/1.00      | m1_subset_1(sK5(sK9,sK11,sK8),u1_struct_0(sK9)) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_14254,c_8225]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_7,plain,
% 3.93/1.00      ( sP0(X0,X1,X2) | ~ r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2)) ),
% 3.93/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1388,plain,
% 3.93/1.00      ( sP0(sK9,sK11,sK8)
% 3.93/1.00      | ~ r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1407,plain,
% 3.93/1.00      ( sP0(sK9,sK11,sK8) = iProver_top
% 3.93/1.00      | r1_orders_2(sK9,sK4(sK9,sK11,sK8),sK5(sK9,sK11,sK8)) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1388]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(contradiction,plain,
% 3.93/1.00      ( $false ),
% 3.93/1.00      inference(minisat,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_14261,c_1407,c_1395,c_1255,c_1227,c_43,c_41,c_40,c_39,
% 3.93/1.00                 c_35,c_34]) ).
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  ------                               Statistics
% 3.93/1.00  
% 3.93/1.00  ------ Selected
% 3.93/1.00  
% 3.93/1.00  total_time:                             0.442
% 3.93/1.00  
%------------------------------------------------------------------------------
