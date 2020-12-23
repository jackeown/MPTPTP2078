%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2050+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:05 EST 2020

% Result     : Theorem 35.65s
% Output     : CNFRefutation 35.65s
% Verified   : 
% Statistics : Number of formulae       :  312 (2568 expanded)
%              Number of clauses        :  197 ( 661 expanded)
%              Number of leaves         :   30 ( 767 expanded)
%              Depth                    :   31
%              Number of atoms          : 1749 (18184 expanded)
%              Number of equality atoms :  449 (1224 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   22 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f59])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK3(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK2(X0,X1,X2,X3))
        & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK2(X0,X1,X2,X3))
                      & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK3(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f60,f62,f61])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_yellow19(X2,X0,X1)
             => r1_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_yellow19(X2,X0,X1)
               => r1_waybel_0(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_waybel_0(X0,X1,X2)
              & m1_yellow19(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_waybel_0(X0,X1,X2)
              & m1_yellow19(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_waybel_0(X0,X1,X2)
          & m1_yellow19(X2,X0,X1) )
     => ( ~ r1_waybel_0(X0,X1,sK10)
        & m1_yellow19(sK10,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_waybel_0(X0,X1,X2)
              & m1_yellow19(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r1_waybel_0(X0,sK9,X2)
            & m1_yellow19(X2,X0,sK9) )
        & l1_waybel_0(sK9,X0)
        & v7_waybel_0(sK9)
        & v4_orders_2(sK9)
        & ~ v2_struct_0(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_waybel_0(X0,X1,X2)
                & m1_yellow19(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_waybel_0(sK8,X1,X2)
              & m1_yellow19(X2,sK8,X1) )
          & l1_waybel_0(X1,sK8)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,
    ( ~ r1_waybel_0(sK8,sK9,sK10)
    & m1_yellow19(sK10,sK8,sK9)
    & l1_waybel_0(sK9,sK8)
    & v7_waybel_0(sK9)
    & v4_orders_2(sK9)
    & ~ v2_struct_0(sK9)
    & l1_struct_0(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f55,f79,f78,f77])).

fof(f126,plain,(
    l1_struct_0(sK8) ),
    inference(cnf_transformation,[],[f80])).

fof(f125,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f80])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | r1_orders_2(X1,X3,sK2(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f57,plain,(
    ! [X2,X0,X1,X3] :
      ( ( k4_waybel_9(X0,X1,X2) = X3
      <=> sP0(X3,X1,X0,X2) )
      | ~ sP1(X2,X0,X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f68,plain,(
    ! [X2,X0,X1,X3] :
      ( ( ( k4_waybel_9(X0,X1,X2) = X3
          | ~ sP0(X3,X1,X0,X2) )
        & ( sP0(X3,X1,X0,X2)
          | k4_waybel_9(X0,X1,X2) != X3 ) )
      | ~ sP1(X2,X0,X1,X3) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k4_waybel_9(X1,X2,X0) = X3
          | ~ sP0(X3,X2,X1,X0) )
        & ( sP0(X3,X2,X1,X0)
          | k4_waybel_9(X1,X2,X0) != X3 ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f68])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0)
      | k4_waybel_9(X1,X2,X0) != X3
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0)
      | ~ sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X3,X1,X0,X2] :
      ( sP0(X3,X1,X0,X2)
    <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
        & ! [X4] :
            ( r2_hidden(X4,u1_struct_0(X3))
          <=> ? [X5] :
                ( r1_orders_2(X1,X2,X5)
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP1(X2,X0,X1,X3)
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f27,f57,f56])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X0,X1,X3)
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X3,X1,X0,X2] :
      ( ( sP0(X3,X1,X0,X2)
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
        | ~ sP0(X3,X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f71,plain,(
    ! [X3,X1,X0,X2] :
      ( ( sP0(X3,X1,X0,X2)
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
        | ~ sP0(X3,X1,X0,X2) ) ) ),
    inference(flattening,[],[f70])).

fof(f72,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | u1_waybel_0(X2,X0) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0))
        | ~ r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)))
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_orders_2(X1,X3,X5)
                  | X4 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              | ~ r2_hidden(X4,u1_struct_0(X0)) )
            & ( ? [X6] :
                  ( r1_orders_2(X1,X3,X6)
                  & X4 = X6
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              | r2_hidden(X4,u1_struct_0(X0)) ) ) )
      & ( ( u1_waybel_0(X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0))
          & r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)))
          & ! [X7] :
              ( ( r2_hidden(X7,u1_struct_0(X0))
                | ! [X8] :
                    ( ~ r1_orders_2(X1,X3,X8)
                    | X7 != X8
                    | ~ m1_subset_1(X8,u1_struct_0(X1)) ) )
              & ( ? [X9] :
                    ( r1_orders_2(X1,X3,X9)
                    & X7 = X9
                    & m1_subset_1(X9,u1_struct_0(X1)) )
                | ~ r2_hidden(X7,u1_struct_0(X0)) ) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f71])).

fof(f75,plain,(
    ! [X7,X3,X1] :
      ( ? [X9] :
          ( r1_orders_2(X1,X3,X9)
          & X7 = X9
          & m1_subset_1(X9,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X3,sK7(X1,X3,X7))
        & sK7(X1,X3,X7) = X7
        & m1_subset_1(sK7(X1,X3,X7),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X4,X3,X1,X0] :
      ( ? [X6] :
          ( r1_orders_2(X1,X3,X6)
          & X4 = X6
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X3,sK6(X0,X1,X3))
        & sK6(X0,X1,X3) = X4
        & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_orders_2(X1,X3,X5)
                | X4 != X5
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r2_hidden(X4,u1_struct_0(X0)) )
          & ( ? [X6] :
                ( r1_orders_2(X1,X3,X6)
                & X4 = X6
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | r2_hidden(X4,u1_struct_0(X0)) ) )
     => ( ( ! [X5] :
              ( ~ r1_orders_2(X1,X3,X5)
              | sK5(X0,X1,X3) != X5
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(sK5(X0,X1,X3),u1_struct_0(X0)) )
        & ( ? [X6] :
              ( r1_orders_2(X1,X3,X6)
              & sK5(X0,X1,X3) = X6
              & m1_subset_1(X6,u1_struct_0(X1)) )
          | r2_hidden(sK5(X0,X1,X3),u1_struct_0(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | u1_waybel_0(X2,X0) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0))
        | ~ r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)))
        | ( ( ! [X5] :
                ( ~ r1_orders_2(X1,X3,X5)
                | sK5(X0,X1,X3) != X5
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r2_hidden(sK5(X0,X1,X3),u1_struct_0(X0)) )
          & ( ( r1_orders_2(X1,X3,sK6(X0,X1,X3))
              & sK5(X0,X1,X3) = sK6(X0,X1,X3)
              & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X1)) )
            | r2_hidden(sK5(X0,X1,X3),u1_struct_0(X0)) ) ) )
      & ( ( u1_waybel_0(X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0))
          & r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)))
          & ! [X7] :
              ( ( r2_hidden(X7,u1_struct_0(X0))
                | ! [X8] :
                    ( ~ r1_orders_2(X1,X3,X8)
                    | X7 != X8
                    | ~ m1_subset_1(X8,u1_struct_0(X1)) ) )
              & ( ( r1_orders_2(X1,X3,sK7(X1,X3,X7))
                  & sK7(X1,X3,X7) = X7
                  & m1_subset_1(sK7(X1,X3,X7),u1_struct_0(X1)) )
                | ~ r2_hidden(X7,u1_struct_0(X0)) ) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f72,f75,f74,f73])).

fof(f95,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,u1_struct_0(X0))
      | ~ r1_orders_2(X1,X3,X8)
      | X7 != X8
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f137,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,u1_struct_0(X0))
      | ~ r1_orders_2(X1,X3,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f95])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f121,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f132,plain,(
    ~ r1_waybel_0(sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f80])).

fof(f127,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f80])).

fof(f130,plain,(
    l1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f80])).

fof(f131,plain,(
    m1_yellow19(sK10,sK8,sK9) ),
    inference(cnf_transformation,[],[f80])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ? [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                      & m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ? [X4] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X4)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X4))) = X2
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f64])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X4)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X4))) = X2
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK4(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK4(X0,X1,X2)))) = X2
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK4(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK4(X0,X1,X2)))) = X2
                    & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f65,f66])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_yellow19(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow19(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_yellow19(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_yellow19(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_yellow19(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => k4_waybel_9(X0,X1,X2) = k5_waybel_9(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k4_waybel_9(X0,X1,X2) = k5_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k4_waybel_9(X0,X1,X2) = k5_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k4_waybel_9(X0,X1,X2) = k5_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f128,plain,(
    v4_orders_2(sK9) ),
    inference(cnf_transformation,[],[f80])).

fof(f129,plain,(
    v7_waybel_0(sK9) ),
    inference(cnf_transformation,[],[f80])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f120,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f138,plain,(
    ! [X4,X2,X0,X1] :
      ( k2_waybel_0(X0,X1,X4) = k2_waybel_0(X0,k4_waybel_9(X0,X1,X2),X4)
      | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f120])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f116,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK4(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK4(X0,X1,X2)))) = X2
      | ~ m1_yellow19(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f113,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f51])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | o_0_0_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_unfolding,[],[f123,f86])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_49,negated_conjecture,
    ( l1_struct_0(sK8) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_2045,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_49])).

cnf(c_2046,plain,
    ( r1_waybel_0(sK8,X0,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(sK8,X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2045])).

cnf(c_50,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_2050,plain,
    ( v2_struct_0(X0)
    | m1_subset_1(sK2(sK8,X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK8)
    | r1_waybel_0(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2046,c_50])).

cnf(c_2051,plain,
    ( r1_waybel_0(sK8,X0,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(sK8,X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2050])).

cnf(c_5485,plain,
    ( r1_waybel_0(sK8,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK2(sK8,X0,X1,X2),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2051])).

cnf(c_1,plain,
    ( r1_orders_2(X0,X1,sK2(X2,X0,X3,X1))
    | r1_waybel_0(X2,X0,X3)
    | ~ l1_waybel_0(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_struct_0(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2099,plain,
    ( r1_orders_2(X0,X1,sK2(X2,X0,X3,X1))
    | r1_waybel_0(X2,X0,X3)
    | ~ l1_waybel_0(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_49])).

cnf(c_2100,plain,
    ( r1_orders_2(X0,X1,sK2(sK8,X0,X2,X1))
    | r1_waybel_0(sK8,X0,X2)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2099])).

cnf(c_2104,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK8)
    | r1_waybel_0(sK8,X0,X2)
    | r1_orders_2(X0,X1,sK2(sK8,X0,X2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2100,c_50])).

cnf(c_2105,plain,
    ( r1_orders_2(X0,X1,sK2(sK8,X0,X2,X1))
    | r1_waybel_0(sK8,X0,X2)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2104])).

cnf(c_5483,plain,
    ( r1_orders_2(X0,X1,sK2(sK8,X0,X2,X1)) = iProver_top
    | r1_waybel_0(sK8,X0,X2) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2105])).

cnf(c_9,plain,
    ( ~ sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0))
    | sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_20,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ v6_waybel_0(X3,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2477,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ v6_waybel_0(X3,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_49])).

cnf(c_2478,plain,
    ( sP1(X0,sK8,X1,X2)
    | ~ v6_waybel_0(X2,sK8)
    | ~ l1_waybel_0(X1,sK8)
    | ~ l1_waybel_0(X2,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2477])).

cnf(c_2482,plain,
    ( v2_struct_0(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,sK8)
    | ~ l1_waybel_0(X1,sK8)
    | ~ v6_waybel_0(X2,sK8)
    | sP1(X0,sK8,X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2478,c_50])).

cnf(c_2483,plain,
    ( sP1(X0,sK8,X1,X2)
    | ~ v6_waybel_0(X2,sK8)
    | ~ l1_waybel_0(X1,sK8)
    | ~ l1_waybel_0(X2,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_2482])).

cnf(c_2702,plain,
    ( sP0(k4_waybel_9(X0,X1,X2),X1,X0,X2)
    | ~ v6_waybel_0(X3,sK8)
    | ~ l1_waybel_0(X3,sK8)
    | ~ l1_waybel_0(X4,sK8)
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | v2_struct_0(X4)
    | X5 != X2
    | X4 != X1
    | k4_waybel_9(X0,X1,X2) != X3
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_2483])).

cnf(c_2703,plain,
    ( sP0(k4_waybel_9(sK8,X0,X1),X0,sK8,X1)
    | ~ v6_waybel_0(k4_waybel_9(sK8,X0,X1),sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ l1_waybel_0(k4_waybel_9(sK8,X0,X1),sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_2702])).

cnf(c_23,plain,
    ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1970,plain,
    ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_49])).

cnf(c_1971,plain,
    ( v6_waybel_0(k4_waybel_9(sK8,X0,X1),sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_1970])).

cnf(c_1975,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK8)
    | v6_waybel_0(k4_waybel_9(sK8,X0,X1),sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1971,c_50])).

cnf(c_1976,plain,
    ( v6_waybel_0(k4_waybel_9(sK8,X0,X1),sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1975])).

cnf(c_22,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_waybel_0(k4_waybel_9(X1,X0,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2429,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_waybel_0(k4_waybel_9(X1,X0,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_49])).

cnf(c_2430,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | l1_waybel_0(k4_waybel_9(sK8,X0,X1),sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2429])).

cnf(c_2707,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | sP0(k4_waybel_9(sK8,X0,X1),X0,sK8,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2703,c_50,c_1976,c_2430])).

cnf(c_2708,plain,
    ( sP0(k4_waybel_9(sK8,X0,X1),X0,sK8,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2707])).

cnf(c_5467,plain,
    ( sP0(k4_waybel_9(sK8,X0,X1),X0,sK8,X1) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2708])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | r2_hidden(X4,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_5509,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r1_orders_2(X1,X3,X4) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X4,u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6965,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,u1_struct_0(k4_waybel_9(sK8,X0,X1))) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5467,c_5509])).

cnf(c_39,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_5504,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_8466,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k4_waybel_9(sK8,X0,X1))) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6965,c_5504])).

cnf(c_21,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2) = k2_waybel_0(X1,X0,X2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2453,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2) = k2_waybel_0(X1,X0,X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_49])).

cnf(c_2454,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0),X1) = k2_waybel_0(sK8,X0,X1) ),
    inference(unflattening,[status(thm)],[c_2453])).

cnf(c_2458,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK8)
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0),X1) = k2_waybel_0(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2454,c_50])).

cnf(c_2459,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0),X1) = k2_waybel_0(sK8,X0,X1) ),
    inference(renaming,[status(thm)],[c_2458])).

cnf(c_5470,plain,
    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0),X1) = k2_waybel_0(sK8,X0,X1)
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2459])).

cnf(c_8924,plain,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(sK8,X0,X1)),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,X0,X1)),X2) = k2_waybel_0(sK8,k4_waybel_9(sK8,X0,X1),X2)
    | r1_orders_2(X0,X1,X2) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | l1_waybel_0(k4_waybel_9(sK8,X0,X1),sK8) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k4_waybel_9(sK8,X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8466,c_5470])).

cnf(c_51,plain,
    ( v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_2431,plain,
    ( l1_waybel_0(X0,sK8) != iProver_top
    | l1_waybel_0(k4_waybel_9(sK8,X0,X1),sK8) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2430])).

cnf(c_16567,plain,
    ( l1_waybel_0(X0,sK8) != iProver_top
    | r1_orders_2(X0,X1,X2) != iProver_top
    | k3_funct_2(u1_struct_0(k4_waybel_9(sK8,X0,X1)),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,X0,X1)),X2) = k2_waybel_0(sK8,k4_waybel_9(sK8,X0,X1),X2)
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k4_waybel_9(sK8,X0,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8924,c_51,c_2431])).

cnf(c_16568,plain,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(sK8,X0,X1)),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,X0,X1)),X2) = k2_waybel_0(sK8,k4_waybel_9(sK8,X0,X1),X2)
    | r1_orders_2(X0,X1,X2) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k4_waybel_9(sK8,X0,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_16567])).

cnf(c_16573,plain,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(sK8,X0,X1)),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,X0,X1)),sK2(sK8,X0,X2,X1)) = k2_waybel_0(sK8,k4_waybel_9(sK8,X0,X1),sK2(sK8,X0,X2,X1))
    | r1_waybel_0(sK8,X0,X2) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK2(sK8,X0,X2,X1),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k4_waybel_9(sK8,X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5483,c_16568])).

cnf(c_62561,plain,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(sK8,X0,X1)),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,X0,X1)),sK2(sK8,X0,X2,X1)) = k2_waybel_0(sK8,k4_waybel_9(sK8,X0,X1),sK2(sK8,X0,X2,X1))
    | r1_waybel_0(sK8,X0,X2) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k4_waybel_9(sK8,X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5485,c_16573])).

cnf(c_43,negated_conjecture,
    ( ~ r1_waybel_0(sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_5501,plain,
    ( r1_waybel_0(sK8,sK9,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_62674,plain,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(sK8,sK9,X0)),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,X0)),sK2(sK8,sK9,sK10,X0)) = k2_waybel_0(sK8,k4_waybel_9(sK8,sK9,X0),sK2(sK8,sK9,sK10,X0))
    | l1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | v2_struct_0(k4_waybel_9(sK8,sK9,X0)) = iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_62561,c_5501])).

cnf(c_48,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_53,plain,
    ( v2_struct_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_45,negated_conjecture,
    ( l1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_56,plain,
    ( l1_waybel_0(sK9,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_62791,plain,
    ( v2_struct_0(k4_waybel_9(sK8,sK9,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | k3_funct_2(u1_struct_0(k4_waybel_9(sK8,sK9,X0)),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,X0)),sK2(sK8,sK9,sK10,X0)) = k2_waybel_0(sK8,k4_waybel_9(sK8,sK9,X0),sK2(sK8,sK9,sK10,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_62674,c_53,c_56])).

cnf(c_62792,plain,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(sK8,sK9,X0)),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,X0)),sK2(sK8,sK9,sK10,X0)) = k2_waybel_0(sK8,k4_waybel_9(sK8,sK9,X0),sK2(sK8,sK9,sK10,X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | v2_struct_0(k4_waybel_9(sK8,sK9,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_62791])).

cnf(c_44,negated_conjecture,
    ( m1_yellow19(sK10,sK8,sK9) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_5500,plain,
    ( m1_yellow19(sK10,sK8,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_7,plain,
    ( ~ m1_yellow19(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK4(X1,X2,X0),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_26,plain,
    ( ~ m1_yellow19(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_324,plain,
    ( ~ l1_waybel_0(X2,X1)
    | ~ m1_yellow19(X0,X1,X2)
    | m1_subset_1(sK4(X1,X2,X0),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_26])).

cnf(c_325,plain,
    ( ~ m1_yellow19(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | m1_subset_1(sK4(X1,X2,X0),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_324])).

cnf(c_2306,plain,
    ( ~ m1_yellow19(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | m1_subset_1(sK4(X1,X2,X0),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_325,c_49])).

cnf(c_2307,plain,
    ( ~ m1_yellow19(X0,sK8,X1)
    | ~ l1_waybel_0(X1,sK8)
    | m1_subset_1(sK4(sK8,X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2306])).

cnf(c_2311,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(sK4(sK8,X1,X0),u1_struct_0(X1))
    | ~ l1_waybel_0(X1,sK8)
    | ~ m1_yellow19(X0,sK8,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2307,c_50])).

cnf(c_2312,plain,
    ( ~ m1_yellow19(X0,sK8,X1)
    | ~ l1_waybel_0(X1,sK8)
    | m1_subset_1(sK4(sK8,X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_2311])).

cnf(c_5476,plain,
    ( m1_yellow19(X0,sK8,X1) != iProver_top
    | l1_waybel_0(X1,sK8) != iProver_top
    | m1_subset_1(sK4(sK8,X1,X0),u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2312])).

cnf(c_37,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | k5_waybel_9(X1,X0,X2) = k4_waybel_9(X1,X0,X2) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2363,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k5_waybel_9(X1,X0,X2) = k4_waybel_9(X1,X0,X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_49])).

cnf(c_2364,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | k5_waybel_9(sK8,X0,X1) = k4_waybel_9(sK8,X0,X1) ),
    inference(unflattening,[status(thm)],[c_2363])).

cnf(c_2368,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK8)
    | k5_waybel_9(sK8,X0,X1) = k4_waybel_9(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2364,c_50])).

cnf(c_2369,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k5_waybel_9(sK8,X0,X1) = k4_waybel_9(sK8,X0,X1) ),
    inference(renaming,[status(thm)],[c_2368])).

cnf(c_5474,plain,
    ( k5_waybel_9(sK8,X0,X1) = k4_waybel_9(sK8,X0,X1)
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2369])).

cnf(c_7171,plain,
    ( k5_waybel_9(sK8,X0,sK4(sK8,X0,X1)) = k4_waybel_9(sK8,X0,sK4(sK8,X0,X1))
    | m1_yellow19(X1,sK8,X0) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5476,c_5474])).

cnf(c_8797,plain,
    ( k5_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)) = k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))
    | l1_waybel_0(sK9,sK8) != iProver_top
    | v4_orders_2(sK9) != iProver_top
    | v7_waybel_0(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_5500,c_7171])).

cnf(c_47,negated_conjecture,
    ( v4_orders_2(sK9) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_46,negated_conjecture,
    ( v7_waybel_0(sK9) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_1103,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK4(X1,X0,X2),u1_struct_0(X0))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | sK10 != X2
    | sK9 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_325,c_44])).

cnf(c_1104,plain,
    ( ~ l1_waybel_0(sK9,sK8)
    | m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9))
    | ~ l1_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_1103])).

cnf(c_5771,plain,
    ( ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | k5_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)) = k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_2369])).

cnf(c_8800,plain,
    ( k5_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)) = k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8797,c_50,c_49,c_48,c_47,c_46,c_45,c_1104,c_5771])).

cnf(c_24,plain,
    ( m2_yellow_6(k5_waybel_9(X0,X1,X2),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_30,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1142,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | X3 != X1
    | X2 != X0
    | k5_waybel_9(X1,X0,X4) != X5 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_1143,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k5_waybel_9(X1,X0,X2)) ),
    inference(unflattening,[status(thm)],[c_1142])).

cnf(c_2216,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k5_waybel_9(X1,X0,X2))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1143,c_49])).

cnf(c_2217,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k5_waybel_9(sK8,X0,X1))
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2216])).

cnf(c_2221,plain,
    ( ~ v2_struct_0(k5_waybel_9(sK8,X0,X1))
    | v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2217,c_50])).

cnf(c_2222,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k5_waybel_9(sK8,X0,X1)) ),
    inference(renaming,[status(thm)],[c_2221])).

cnf(c_5479,plain,
    ( l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k5_waybel_9(sK8,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2222])).

cnf(c_8806,plain,
    ( l1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9)) != iProver_top
    | v4_orders_2(sK9) != iProver_top
    | v7_waybel_0(sK9) != iProver_top
    | v2_struct_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_8800,c_5479])).

cnf(c_52,plain,
    ( l1_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_54,plain,
    ( v4_orders_2(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_55,plain,
    ( v7_waybel_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_1105,plain,
    ( l1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9)) = iProver_top
    | l1_struct_0(sK8) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1104])).

cnf(c_8860,plain,
    ( v2_struct_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8806,c_51,c_52,c_53,c_54,c_55,c_56,c_1105])).

cnf(c_62798,plain,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10))) = k2_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)),sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)))
    | m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_62792,c_8860])).

cnf(c_38,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(k4_waybel_9(X1,X0,X2)))
    | ~ v7_waybel_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | k2_waybel_0(X1,k4_waybel_9(X1,X0,X2),X3) = k2_waybel_0(X1,X0,X3) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_2330,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k4_waybel_9(X1,X0,X3)))
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k2_waybel_0(X1,k4_waybel_9(X1,X0,X3),X2) = k2_waybel_0(X1,X0,X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_49])).

cnf(c_2331,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k4_waybel_9(sK8,X0,X1)))
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | k2_waybel_0(sK8,k4_waybel_9(sK8,X0,X1),X2) = k2_waybel_0(sK8,X0,X2) ),
    inference(unflattening,[status(thm)],[c_2330])).

cnf(c_2335,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ m1_subset_1(X2,u1_struct_0(k4_waybel_9(sK8,X0,X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK8)
    | k2_waybel_0(sK8,k4_waybel_9(sK8,X0,X1),X2) = k2_waybel_0(sK8,X0,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2331,c_50])).

cnf(c_2336,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k4_waybel_9(sK8,X0,X1)))
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k2_waybel_0(sK8,k4_waybel_9(sK8,X0,X1),X2) = k2_waybel_0(sK8,X0,X2) ),
    inference(renaming,[status(thm)],[c_2335])).

cnf(c_5475,plain,
    ( k2_waybel_0(sK8,k4_waybel_9(sK8,X0,X1),X2) = k2_waybel_0(sK8,X0,X2)
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k4_waybel_9(sK8,X0,X1))) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2336])).

cnf(c_8927,plain,
    ( k2_waybel_0(sK8,k4_waybel_9(sK8,X0,X1),X2) = k2_waybel_0(sK8,X0,X2)
    | r1_orders_2(X0,X1,X2) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8466,c_5475])).

cnf(c_9565,plain,
    ( k2_waybel_0(sK8,k4_waybel_9(sK8,X0,X1),sK2(sK8,X0,X2,X1)) = k2_waybel_0(sK8,X0,sK2(sK8,X0,X2,X1))
    | r1_waybel_0(sK8,X0,X2) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK2(sK8,X0,X2,X1),u1_struct_0(X0)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5483,c_8927])).

cnf(c_14556,plain,
    ( k2_waybel_0(sK8,k4_waybel_9(sK8,X0,X1),sK2(sK8,X0,X2,X1)) = k2_waybel_0(sK8,X0,sK2(sK8,X0,X2,X1))
    | r1_waybel_0(sK8,X0,X2) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5485,c_9565])).

cnf(c_14921,plain,
    ( k2_waybel_0(sK8,k4_waybel_9(sK8,X0,sK4(sK8,X0,X1)),sK2(sK8,X0,X2,sK4(sK8,X0,X1))) = k2_waybel_0(sK8,X0,sK2(sK8,X0,X2,sK4(sK8,X0,X1)))
    | m1_yellow19(X1,sK8,X0) != iProver_top
    | r1_waybel_0(sK8,X0,X2) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5476,c_14556])).

cnf(c_15179,plain,
    ( k2_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)),sK2(sK8,sK9,X0,sK4(sK8,sK9,sK10))) = k2_waybel_0(sK8,sK9,sK2(sK8,sK9,X0,sK4(sK8,sK9,sK10)))
    | r1_waybel_0(sK8,sK9,X0) = iProver_top
    | l1_waybel_0(sK9,sK8) != iProver_top
    | v7_waybel_0(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_5500,c_14921])).

cnf(c_15184,plain,
    ( r1_waybel_0(sK8,sK9,X0) = iProver_top
    | k2_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)),sK2(sK8,sK9,X0,sK4(sK8,sK9,sK10))) = k2_waybel_0(sK8,sK9,sK2(sK8,sK9,X0,sK4(sK8,sK9,sK10))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15179,c_53,c_55,c_56])).

cnf(c_15185,plain,
    ( k2_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)),sK2(sK8,sK9,X0,sK4(sK8,sK9,sK10))) = k2_waybel_0(sK8,sK9,sK2(sK8,sK9,X0,sK4(sK8,sK9,sK10)))
    | r1_waybel_0(sK8,sK9,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_15184])).

cnf(c_15190,plain,
    ( k2_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)),sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10))) = k2_waybel_0(sK8,sK9,sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10))) ),
    inference(superposition,[status(thm)],[c_15185,c_5501])).

cnf(c_33,plain,
    ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_610,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | k3_funct_2(X3,X5,X4,X2) = k1_funct_1(X4,X2)
    | u1_waybel_0(X1,X0) != X4
    | u1_struct_0(X0) != X3
    | u1_struct_0(X1) != X5 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_36])).

cnf(c_611,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(u1_waybel_0(X1,X0))
    | v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X1)
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2) = k1_funct_1(u1_waybel_0(X1,X0),X2) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_34,plain,
    ( ~ l1_waybel_0(X0,X1)
    | v1_funct_1(u1_waybel_0(X1,X0))
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_32,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_615,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X1)
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2) = k1_funct_1(u1_waybel_0(X1,X0),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_611,c_34,c_32])).

cnf(c_2246,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X0))
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2) = k1_funct_1(u1_waybel_0(X1,X0),X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_615,c_49])).

cnf(c_2247,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X0))
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0),X1) = k1_funct_1(u1_waybel_0(sK8,X0),X1) ),
    inference(unflattening,[status(thm)],[c_2246])).

cnf(c_5478,plain,
    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0),X1) = k1_funct_1(u1_waybel_0(sK8,X0),X1)
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2247])).

cnf(c_8923,plain,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(sK8,X0,X1)),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,X0,X1)),X2) = k1_funct_1(u1_waybel_0(sK8,k4_waybel_9(sK8,X0,X1)),X2)
    | r1_orders_2(X0,X1,X2) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | l1_waybel_0(k4_waybel_9(sK8,X0,X1),sK8) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v1_xboole_0(u1_struct_0(k4_waybel_9(sK8,X0,X1))) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8466,c_5478])).

cnf(c_42,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_5502,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_8467,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v1_xboole_0(u1_struct_0(k4_waybel_9(sK8,X0,X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6965,c_5502])).

cnf(c_18451,plain,
    ( m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | k3_funct_2(u1_struct_0(k4_waybel_9(sK8,X0,X1)),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,X0,X1)),X2) = k1_funct_1(u1_waybel_0(sK8,k4_waybel_9(sK8,X0,X1)),X2)
    | r1_orders_2(X0,X1,X2) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8923,c_51,c_2431,c_8467])).

cnf(c_18452,plain,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(sK8,X0,X1)),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,X0,X1)),X2) = k1_funct_1(u1_waybel_0(sK8,k4_waybel_9(sK8,X0,X1)),X2)
    | r1_orders_2(X0,X1,X2) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_18451])).

cnf(c_18457,plain,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(sK8,X0,X1)),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,X0,X1)),sK2(sK8,X0,X2,X1)) = k1_funct_1(u1_waybel_0(sK8,k4_waybel_9(sK8,X0,X1)),sK2(sK8,X0,X2,X1))
    | r1_waybel_0(sK8,X0,X2) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK2(sK8,X0,X2,X1),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5483,c_18452])).

cnf(c_23492,plain,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(sK8,X0,X1)),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,X0,X1)),sK2(sK8,X0,X2,X1)) = k1_funct_1(u1_waybel_0(sK8,k4_waybel_9(sK8,X0,X1)),sK2(sK8,X0,X2,X1))
    | r1_waybel_0(sK8,X0,X2) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5485,c_18457])).

cnf(c_23500,plain,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(sK8,X0,sK4(sK8,X0,X1))),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,X0,sK4(sK8,X0,X1))),sK2(sK8,X0,X2,sK4(sK8,X0,X1))) = k1_funct_1(u1_waybel_0(sK8,k4_waybel_9(sK8,X0,sK4(sK8,X0,X1))),sK2(sK8,X0,X2,sK4(sK8,X0,X1)))
    | m1_yellow19(X1,sK8,X0) != iProver_top
    | r1_waybel_0(sK8,X0,X2) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5476,c_23492])).

cnf(c_26109,plain,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),sK2(sK8,sK9,X0,sK4(sK8,sK9,sK10))) = k1_funct_1(u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),sK2(sK8,sK9,X0,sK4(sK8,sK9,sK10)))
    | r1_waybel_0(sK8,sK9,X0) = iProver_top
    | l1_waybel_0(sK9,sK8) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_5500,c_23500])).

cnf(c_26253,plain,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),sK2(sK8,sK9,X0,sK4(sK8,sK9,sK10))) = k1_funct_1(u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),sK2(sK8,sK9,X0,sK4(sK8,sK9,sK10)))
    | r1_waybel_0(sK8,sK9,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26109,c_53,c_56])).

cnf(c_26259,plain,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10))) = k1_funct_1(u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10))) ),
    inference(superposition,[status(thm)],[c_26253,c_5501])).

cnf(c_62805,plain,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10))) = k2_waybel_0(sK8,sK9,sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)))
    | m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_62798,c_15190,c_26259])).

cnf(c_62806,plain,
    ( k1_funct_1(u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10))) = k2_waybel_0(sK8,sK9,sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)))
    | m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_62805,c_26259])).

cnf(c_62927,plain,
    ( k1_funct_1(u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10))) = k2_waybel_0(sK8,sK9,sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_62806,c_51,c_52,c_53,c_56,c_1105])).

cnf(c_6,plain,
    ( ~ m1_yellow19(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_relset_1(u1_struct_0(k4_waybel_9(X1,X2,sK4(X1,X2,X0))),u1_struct_0(X1),u1_waybel_0(X1,k4_waybel_9(X1,X2,sK4(X1,X2,X0)))) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_331,plain,
    ( ~ l1_waybel_0(X2,X1)
    | ~ m1_yellow19(X0,X1,X2)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_relset_1(u1_struct_0(k4_waybel_9(X1,X2,sK4(X1,X2,X0))),u1_struct_0(X1),u1_waybel_0(X1,k4_waybel_9(X1,X2,sK4(X1,X2,X0)))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_26])).

cnf(c_332,plain,
    ( ~ m1_yellow19(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_relset_1(u1_struct_0(k4_waybel_9(X1,X2,sK4(X1,X2,X0))),u1_struct_0(X1),u1_waybel_0(X1,k4_waybel_9(X1,X2,sK4(X1,X2,X0)))) = X0 ),
    inference(renaming,[status(thm)],[c_331])).

cnf(c_2282,plain,
    ( ~ m1_yellow19(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_relset_1(u1_struct_0(k4_waybel_9(X1,X2,sK4(X1,X2,X0))),u1_struct_0(X1),u1_waybel_0(X1,k4_waybel_9(X1,X2,sK4(X1,X2,X0)))) = X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_332,c_49])).

cnf(c_2283,plain,
    ( ~ m1_yellow19(X0,sK8,X1)
    | ~ l1_waybel_0(X1,sK8)
    | v2_struct_0(X1)
    | v2_struct_0(sK8)
    | k2_relset_1(u1_struct_0(k4_waybel_9(sK8,X1,sK4(sK8,X1,X0))),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,X1,sK4(sK8,X1,X0)))) = X0 ),
    inference(unflattening,[status(thm)],[c_2282])).

cnf(c_2287,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK8)
    | ~ m1_yellow19(X0,sK8,X1)
    | k2_relset_1(u1_struct_0(k4_waybel_9(sK8,X1,sK4(sK8,X1,X0))),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,X1,sK4(sK8,X1,X0)))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2283,c_50])).

cnf(c_2288,plain,
    ( ~ m1_yellow19(X0,sK8,X1)
    | ~ l1_waybel_0(X1,sK8)
    | v2_struct_0(X1)
    | k2_relset_1(u1_struct_0(k4_waybel_9(sK8,X1,sK4(sK8,X1,X0))),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,X1,sK4(sK8,X1,X0)))) = X0 ),
    inference(renaming,[status(thm)],[c_2287])).

cnf(c_5477,plain,
    ( k2_relset_1(u1_struct_0(k4_waybel_9(sK8,X0,sK4(sK8,X0,X1))),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,X0,sK4(sK8,X0,X1)))) = X1
    | m1_yellow19(X1,sK8,X0) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2288])).

cnf(c_7182,plain,
    ( k2_relset_1(u1_struct_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)))) = sK10
    | l1_waybel_0(sK9,sK8) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_5500,c_5477])).

cnf(c_1095,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | k2_relset_1(u1_struct_0(k4_waybel_9(X1,X0,sK4(X1,X0,X2))),u1_struct_0(X1),u1_waybel_0(X1,k4_waybel_9(X1,X0,sK4(X1,X0,X2)))) = X2
    | sK10 != X2
    | sK9 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_332,c_44])).

cnf(c_1096,plain,
    ( ~ l1_waybel_0(sK9,sK8)
    | ~ l1_struct_0(sK8)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8)
    | k2_relset_1(u1_struct_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)))) = sK10 ),
    inference(unflattening,[status(thm)],[c_1095])).

cnf(c_7468,plain,
    ( k2_relset_1(u1_struct_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),u1_struct_0(sK8),u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)))) = sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7182,c_50,c_49,c_48,c_45,c_1096])).

cnf(c_31,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_35,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1929,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_49])).

cnf(c_1930,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK8))
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_1929])).

cnf(c_1932,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1930,c_50])).

cnf(c_2758,plain,
    ( u1_struct_0(sK8) != o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_1932])).

cnf(c_41,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_583,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ r2_hidden(X5,X3)
    | r2_hidden(k1_funct_1(X2,X5),k2_relset_1(X3,X4,X2))
    | ~ v1_funct_1(X2)
    | ~ l1_struct_0(X1)
    | u1_waybel_0(X1,X0) != X2
    | u1_struct_0(X0) != X3
    | u1_struct_0(X1) != X4
    | o_0_0_xboole_0 = X4 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_41])).

cnf(c_584,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | r2_hidden(k1_funct_1(u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ v1_funct_1(u1_waybel_0(X1,X0))
    | ~ l1_struct_0(X1)
    | o_0_0_xboole_0 = u1_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_588,plain,
    ( r2_hidden(k1_funct_1(u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | o_0_0_xboole_0 = u1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_34,c_32])).

cnf(c_589,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | r2_hidden(k1_funct_1(u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ l1_struct_0(X1)
    | o_0_0_xboole_0 = u1_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_588])).

cnf(c_2264,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | r2_hidden(k1_funct_1(u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | u1_struct_0(X1) = o_0_0_xboole_0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_589,c_49])).

cnf(c_2265,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ r2_hidden(X1,u1_struct_0(X0))
    | r2_hidden(k1_funct_1(u1_waybel_0(sK8,X0),X1),k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)))
    | u1_struct_0(sK8) = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_2264])).

cnf(c_2814,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ r2_hidden(X1,u1_struct_0(X0))
    | r2_hidden(k1_funct_1(u1_waybel_0(sK8,X0),X1),k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2758,c_2265])).

cnf(c_5466,plain,
    ( l1_waybel_0(X0,sK8) != iProver_top
    | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(k1_funct_1(u1_waybel_0(sK8,X0),X1),k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2814])).

cnf(c_7471,plain,
    ( l1_waybel_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)),sK8) != iProver_top
    | r2_hidden(X0,u1_struct_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)))) != iProver_top
    | r2_hidden(k1_funct_1(u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),X0),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_7468,c_5466])).

cnf(c_2434,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | l1_waybel_0(k4_waybel_9(sK8,X0,X1),sK8)
    | ~ l1_waybel_0(X0,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2430,c_50])).

cnf(c_2435,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | l1_waybel_0(k4_waybel_9(sK8,X0,X1),sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2434])).

cnf(c_5779,plain,
    ( l1_waybel_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)),sK8)
    | ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9))
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2435])).

cnf(c_5783,plain,
    ( l1_waybel_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)),sK8) = iProver_top
    | l1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9)) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5779])).

cnf(c_7851,plain,
    ( r2_hidden(X0,u1_struct_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)))) != iProver_top
    | r2_hidden(k1_funct_1(u1_waybel_0(sK8,k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10))),X0),sK10) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7471,c_51,c_52,c_53,c_56,c_1105,c_5783])).

cnf(c_62933,plain,
    ( r2_hidden(sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)),u1_struct_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)))) != iProver_top
    | r2_hidden(k2_waybel_0(sK8,sK9,sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10))),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_62927,c_7851])).

cnf(c_6199,plain,
    ( ~ sP0(X0,sK9,X1,X2)
    | ~ r1_orders_2(sK9,X2,sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)))
    | ~ m1_subset_1(sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)),u1_struct_0(sK9))
    | r2_hidden(sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6426,plain,
    ( ~ sP0(X0,sK9,X1,sK4(sK8,sK9,sK10))
    | ~ r1_orders_2(sK9,sK4(sK8,sK9,sK10),sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)))
    | ~ m1_subset_1(sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)),u1_struct_0(sK9))
    | r2_hidden(sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_6199])).

cnf(c_6971,plain,
    ( ~ sP0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)),sK9,sK8,sK4(sK8,sK9,sK10))
    | ~ r1_orders_2(sK9,sK4(sK8,sK9,sK10),sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)))
    | ~ m1_subset_1(sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)),u1_struct_0(sK9))
    | r2_hidden(sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)),u1_struct_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)))) ),
    inference(instantiation,[status(thm)],[c_6426])).

cnf(c_6972,plain,
    ( sP0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)),sK9,sK8,sK4(sK8,sK9,sK10)) != iProver_top
    | r1_orders_2(sK9,sK4(sK8,sK9,sK10),sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10))) != iProver_top
    | m1_subset_1(sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)),u1_struct_0(sK9)) != iProver_top
    | r2_hidden(sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)),u1_struct_0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6971])).

cnf(c_0,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2072,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_49])).

cnf(c_2073,plain,
    ( r1_waybel_0(sK8,X0,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(k2_waybel_0(sK8,X0,sK2(sK8,X0,X1,X2)),X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2072])).

cnf(c_2077,plain,
    ( v2_struct_0(X0)
    | ~ r2_hidden(k2_waybel_0(sK8,X0,sK2(sK8,X0,X1,X2)),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK8)
    | r1_waybel_0(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2073,c_50])).

cnf(c_2078,plain,
    ( r1_waybel_0(sK8,X0,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(k2_waybel_0(sK8,X0,sK2(sK8,X0,X1,X2)),X1)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2077])).

cnf(c_5813,plain,
    ( r1_waybel_0(sK8,sK9,X0)
    | ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9))
    | ~ r2_hidden(k2_waybel_0(sK8,sK9,sK2(sK8,sK9,X0,sK4(sK8,sK9,sK10))),X0)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2078])).

cnf(c_6020,plain,
    ( r1_waybel_0(sK8,sK9,sK10)
    | ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9))
    | ~ r2_hidden(k2_waybel_0(sK8,sK9,sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10))),sK10)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_5813])).

cnf(c_6021,plain,
    ( r1_waybel_0(sK8,sK9,sK10) = iProver_top
    | l1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9)) != iProver_top
    | r2_hidden(k2_waybel_0(sK8,sK9,sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10))),sK10) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6020])).

cnf(c_5814,plain,
    ( r1_waybel_0(sK8,sK9,X0)
    | ~ l1_waybel_0(sK9,sK8)
    | m1_subset_1(sK2(sK8,sK9,X0,sK4(sK8,sK9,sK10)),u1_struct_0(sK9))
    | ~ m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9))
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2051])).

cnf(c_6017,plain,
    ( r1_waybel_0(sK8,sK9,sK10)
    | ~ l1_waybel_0(sK9,sK8)
    | m1_subset_1(sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)),u1_struct_0(sK9))
    | ~ m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9))
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_5814])).

cnf(c_6018,plain,
    ( r1_waybel_0(sK8,sK9,sK10) = iProver_top
    | l1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)),u1_struct_0(sK9)) = iProver_top
    | m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9)) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6017])).

cnf(c_5770,plain,
    ( r1_orders_2(sK9,sK4(sK8,sK9,sK10),sK2(sK8,sK9,X0,sK4(sK8,sK9,sK10)))
    | r1_waybel_0(sK8,sK9,X0)
    | ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9))
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2105])).

cnf(c_5907,plain,
    ( r1_orders_2(sK9,sK4(sK8,sK9,sK10),sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10)))
    | r1_waybel_0(sK8,sK9,sK10)
    | ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9))
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_5770])).

cnf(c_5908,plain,
    ( r1_orders_2(sK9,sK4(sK8,sK9,sK10),sK2(sK8,sK9,sK10,sK4(sK8,sK9,sK10))) = iProver_top
    | r1_waybel_0(sK8,sK9,sK10) = iProver_top
    | l1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9)) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5907])).

cnf(c_5767,plain,
    ( sP0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)),sK9,sK8,sK4(sK8,sK9,sK10))
    | ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9))
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2708])).

cnf(c_5811,plain,
    ( sP0(k4_waybel_9(sK8,sK9,sK4(sK8,sK9,sK10)),sK9,sK8,sK4(sK8,sK9,sK10)) = iProver_top
    | l1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK4(sK8,sK9,sK10),u1_struct_0(sK9)) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5767])).

cnf(c_58,plain,
    ( r1_waybel_0(sK8,sK9,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_62933,c_6972,c_6021,c_6018,c_5908,c_5811,c_1105,c_58,c_56,c_53,c_52,c_51])).


%------------------------------------------------------------------------------
