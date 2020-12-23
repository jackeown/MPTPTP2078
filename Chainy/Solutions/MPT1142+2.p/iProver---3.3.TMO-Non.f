%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1142+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:01 EST 2020

% Result     : Timeout 58.93s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   95 (1143 expanded)
%              Number of clauses        :   58 ( 271 expanded)
%              Number of leaves         :    9 ( 410 expanded)
%              Depth                    :   21
%              Number of atoms          :  422 (10667 expanded)
%              Number of equality atoms :  132 ( 516 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1880,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1881,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( r2_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X2) )
                        | ( r1_orders_2(X0,X2,X3)
                          & r2_orders_2(X0,X1,X2) ) )
                     => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1880])).

fof(f4054,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1881])).

fof(f4055,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f4054])).

fof(f5720,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_orders_2(X0,X1,X3)
          & ( ( r2_orders_2(X0,X2,X3)
              & r1_orders_2(X0,X1,X2) )
            | ( r1_orders_2(X0,X2,X3)
              & r2_orders_2(X0,X1,X2) ) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,X1,sK692)
        & ( ( r2_orders_2(X0,X2,sK692)
            & r1_orders_2(X0,X1,X2) )
          | ( r1_orders_2(X0,X2,sK692)
            & r2_orders_2(X0,X1,X2) ) )
        & m1_subset_1(sK692,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5719,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_orders_2(X0,X1,X3)
              & ( ( r2_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X2) )
                | ( r1_orders_2(X0,X2,X3)
                  & r2_orders_2(X0,X1,X2) ) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_orders_2(X0,X1,X3)
            & ( ( r2_orders_2(X0,sK691,X3)
                & r1_orders_2(X0,X1,sK691) )
              | ( r1_orders_2(X0,sK691,X3)
                & r2_orders_2(X0,X1,sK691) ) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK691,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5718,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_orders_2(X0,sK690,X3)
                & ( ( r2_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,sK690,X2) )
                  | ( r1_orders_2(X0,X2,X3)
                    & r2_orders_2(X0,sK690,X2) ) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK690,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5717,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_orders_2(X0,X1,X3)
                    & ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(sK689,X1,X3)
                  & ( ( r2_orders_2(sK689,X2,X3)
                      & r1_orders_2(sK689,X1,X2) )
                    | ( r1_orders_2(sK689,X2,X3)
                      & r2_orders_2(sK689,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(sK689)) )
              & m1_subset_1(X2,u1_struct_0(sK689)) )
          & m1_subset_1(X1,u1_struct_0(sK689)) )
      & l1_orders_2(sK689)
      & v5_orders_2(sK689)
      & v4_orders_2(sK689) ) ),
    introduced(choice_axiom,[])).

fof(f5721,plain,
    ( ~ r2_orders_2(sK689,sK690,sK692)
    & ( ( r2_orders_2(sK689,sK691,sK692)
        & r1_orders_2(sK689,sK690,sK691) )
      | ( r1_orders_2(sK689,sK691,sK692)
        & r2_orders_2(sK689,sK690,sK691) ) )
    & m1_subset_1(sK692,u1_struct_0(sK689))
    & m1_subset_1(sK691,u1_struct_0(sK689))
    & m1_subset_1(sK690,u1_struct_0(sK689))
    & l1_orders_2(sK689)
    & v5_orders_2(sK689)
    & v4_orders_2(sK689) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK689,sK690,sK691,sK692])],[f4055,f5720,f5719,f5718,f5717])).

fof(f9404,plain,(
    m1_subset_1(sK692,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f5721])).

fof(f9402,plain,(
    m1_subset_1(sK690,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f5721])).

fof(f9403,plain,(
    m1_subset_1(sK691,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f5721])).

fof(f1861,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4025,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1861])).

fof(f5709,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f4025])).

fof(f5710,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f5709])).

fof(f9374,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f5710])).

fof(f9401,plain,(
    l1_orders_2(sK689) ),
    inference(cnf_transformation,[],[f5721])).

fof(f9405,plain,
    ( r1_orders_2(sK689,sK690,sK691)
    | r2_orders_2(sK689,sK690,sK691) ),
    inference(cnf_transformation,[],[f5721])).

fof(f1876,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4046,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1876])).

fof(f4047,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f4046])).

fof(f9395,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4047])).

fof(f9399,plain,(
    v4_orders_2(sK689) ),
    inference(cnf_transformation,[],[f5721])).

fof(f9408,plain,
    ( r2_orders_2(sK689,sK691,sK692)
    | r1_orders_2(sK689,sK691,sK692) ),
    inference(cnf_transformation,[],[f5721])).

fof(f1875,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4044,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1875])).

fof(f4045,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f4044])).

fof(f9394,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4045])).

fof(f9409,plain,(
    ~ r2_orders_2(sK689,sK690,sK692) ),
    inference(cnf_transformation,[],[f5721])).

fof(f9376,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,X1,X2)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f5710])).

fof(f1879,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4052,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1879])).

fof(f4053,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f4052])).

fof(f9398,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4053])).

fof(f9400,plain,(
    v5_orders_2(sK689) ),
    inference(cnf_transformation,[],[f5721])).

fof(f9407,plain,
    ( r2_orders_2(sK689,sK691,sK692)
    | r2_orders_2(sK689,sK690,sK691) ),
    inference(cnf_transformation,[],[f5721])).

cnf(c_3655,negated_conjecture,
    ( m1_subset_1(sK692,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f9404])).

cnf(c_107057,plain,
    ( m1_subset_1(sK692,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3655])).

cnf(c_3657,negated_conjecture,
    ( m1_subset_1(sK690,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f9402])).

cnf(c_107055,plain,
    ( m1_subset_1(sK690,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3657])).

cnf(c_3656,negated_conjecture,
    ( m1_subset_1(sK691,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f9403])).

cnf(c_107056,plain,
    ( m1_subset_1(sK691,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3656])).

cnf(c_3627,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f9374])).

cnf(c_107084,plain,
    ( r1_orders_2(X0,X1,X2) = iProver_top
    | r2_orders_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3627])).

cnf(c_160972,plain,
    ( r1_orders_2(sK689,X0,sK691) = iProver_top
    | r2_orders_2(sK689,X0,sK691) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_107056,c_107084])).

cnf(c_3658,negated_conjecture,
    ( l1_orders_2(sK689) ),
    inference(cnf_transformation,[],[f9401])).

cnf(c_3663,plain,
    ( l1_orders_2(sK689) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3658])).

cnf(c_163670,plain,
    ( m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top
    | r2_orders_2(sK689,X0,sK691) != iProver_top
    | r1_orders_2(sK689,X0,sK691) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_160972,c_3663])).

cnf(c_163671,plain,
    ( r1_orders_2(sK689,X0,sK691) = iProver_top
    | r2_orders_2(sK689,X0,sK691) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top ),
    inference(renaming,[status(thm)],[c_163670])).

cnf(c_163681,plain,
    ( r1_orders_2(sK689,sK690,sK691) = iProver_top
    | r2_orders_2(sK689,sK690,sK691) != iProver_top ),
    inference(superposition,[status(thm)],[c_107055,c_163671])).

cnf(c_3654,negated_conjecture,
    ( r1_orders_2(sK689,sK690,sK691)
    | r2_orders_2(sK689,sK690,sK691) ),
    inference(cnf_transformation,[],[f9405])).

cnf(c_3667,plain,
    ( r1_orders_2(sK689,sK690,sK691) = iProver_top
    | r2_orders_2(sK689,sK690,sK691) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3654])).

cnf(c_163809,plain,
    ( r1_orders_2(sK689,sK690,sK691) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_163681,c_3667])).

cnf(c_3646,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f9395])).

cnf(c_107066,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | r1_orders_2(X0,X2,X3) != iProver_top
    | r1_orders_2(X0,X1,X3) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3646])).

cnf(c_163814,plain,
    ( r1_orders_2(sK689,sK691,X0) != iProver_top
    | r1_orders_2(sK689,sK690,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top
    | m1_subset_1(sK691,u1_struct_0(sK689)) != iProver_top
    | m1_subset_1(sK690,u1_struct_0(sK689)) != iProver_top
    | v4_orders_2(sK689) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_163809,c_107066])).

cnf(c_3660,negated_conjecture,
    ( v4_orders_2(sK689) ),
    inference(cnf_transformation,[],[f9399])).

cnf(c_3661,plain,
    ( v4_orders_2(sK689) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3660])).

cnf(c_3664,plain,
    ( m1_subset_1(sK690,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3657])).

cnf(c_3665,plain,
    ( m1_subset_1(sK691,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3656])).

cnf(c_171508,plain,
    ( r1_orders_2(sK689,sK691,X0) != iProver_top
    | r1_orders_2(sK689,sK690,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_163814,c_3661,c_3663,c_3664,c_3665])).

cnf(c_171517,plain,
    ( r1_orders_2(sK689,sK691,sK692) != iProver_top
    | r1_orders_2(sK689,sK690,sK692) = iProver_top ),
    inference(superposition,[status(thm)],[c_107057,c_171508])).

cnf(c_160971,plain,
    ( r1_orders_2(sK689,X0,sK692) = iProver_top
    | r2_orders_2(sK689,X0,sK692) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_107057,c_107084])).

cnf(c_163564,plain,
    ( m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top
    | r2_orders_2(sK689,X0,sK692) != iProver_top
    | r1_orders_2(sK689,X0,sK692) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_160971,c_3663])).

cnf(c_163565,plain,
    ( r1_orders_2(sK689,X0,sK692) = iProver_top
    | r2_orders_2(sK689,X0,sK692) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top ),
    inference(renaming,[status(thm)],[c_163564])).

cnf(c_163574,plain,
    ( r1_orders_2(sK689,sK691,sK692) = iProver_top
    | r2_orders_2(sK689,sK691,sK692) != iProver_top ),
    inference(superposition,[status(thm)],[c_107056,c_163565])).

cnf(c_3651,negated_conjecture,
    ( r1_orders_2(sK689,sK691,sK692)
    | r2_orders_2(sK689,sK691,sK692) ),
    inference(cnf_transformation,[],[f9408])).

cnf(c_3670,plain,
    ( r1_orders_2(sK689,sK691,sK692) = iProver_top
    | r2_orders_2(sK689,sK691,sK692) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3651])).

cnf(c_163614,plain,
    ( r1_orders_2(sK689,sK691,sK692) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_163574,c_3670])).

cnf(c_171531,plain,
    ( r1_orders_2(sK689,sK690,sK692) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_171517,c_3670,c_163574])).

cnf(c_3645,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f9394])).

cnf(c_107067,plain,
    ( X0 = X1
    | r1_orders_2(X2,X1,X0) != iProver_top
    | r1_orders_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X2)) != iProver_top
    | v5_orders_2(X2) != iProver_top
    | l1_orders_2(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3645])).

cnf(c_171539,plain,
    ( sK692 = sK690
    | r1_orders_2(sK689,sK692,sK690) != iProver_top
    | m1_subset_1(sK692,u1_struct_0(sK689)) != iProver_top
    | m1_subset_1(sK690,u1_struct_0(sK689)) != iProver_top
    | v5_orders_2(sK689) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_171531,c_107067])).

cnf(c_3666,plain,
    ( m1_subset_1(sK692,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3655])).

cnf(c_3650,negated_conjecture,
    ( ~ r2_orders_2(sK689,sK690,sK692) ),
    inference(cnf_transformation,[],[f9409])).

cnf(c_3671,plain,
    ( r2_orders_2(sK689,sK690,sK692) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3650])).

cnf(c_3625,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f9376])).

cnf(c_107086,plain,
    ( X0 = X1
    | r1_orders_2(X2,X1,X0) != iProver_top
    | r2_orders_2(X2,X1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X2)) != iProver_top
    | l1_orders_2(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3625])).

cnf(c_171538,plain,
    ( sK692 = sK690
    | r2_orders_2(sK689,sK690,sK692) = iProver_top
    | m1_subset_1(sK692,u1_struct_0(sK689)) != iProver_top
    | m1_subset_1(sK690,u1_struct_0(sK689)) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_171531,c_107086])).

cnf(c_173142,plain,
    ( sK692 = sK690 ),
    inference(global_propositional_subsumption,[status(thm)],[c_171539,c_3663,c_3664,c_3666,c_3671,c_171538])).

cnf(c_107061,plain,
    ( r1_orders_2(sK689,sK691,sK692) = iProver_top
    | r2_orders_2(sK689,sK691,sK692) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3651])).

cnf(c_3649,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f9398])).

cnf(c_107063,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | r2_orders_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3649])).

cnf(c_140794,plain,
    ( r2_orders_2(sK689,sK691,sK692) = iProver_top
    | r2_orders_2(sK689,sK692,sK691) != iProver_top
    | m1_subset_1(sK691,u1_struct_0(sK689)) != iProver_top
    | m1_subset_1(sK692,u1_struct_0(sK689)) != iProver_top
    | v5_orders_2(sK689) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_107061,c_107063])).

cnf(c_3659,negated_conjecture,
    ( v5_orders_2(sK689) ),
    inference(cnf_transformation,[],[f9400])).

cnf(c_3662,plain,
    ( v5_orders_2(sK689) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3659])).

cnf(c_141595,plain,
    ( r2_orders_2(sK689,sK691,sK692) = iProver_top
    | r2_orders_2(sK689,sK692,sK691) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_140794,c_3662,c_3663,c_3665,c_3666])).

cnf(c_173165,plain,
    ( r2_orders_2(sK689,sK691,sK690) = iProver_top
    | r2_orders_2(sK689,sK690,sK691) != iProver_top ),
    inference(demodulation,[status(thm)],[c_173142,c_141595])).

cnf(c_3652,negated_conjecture,
    ( r2_orders_2(sK689,sK691,sK692)
    | r2_orders_2(sK689,sK690,sK691) ),
    inference(cnf_transformation,[],[f9407])).

cnf(c_107060,plain,
    ( r2_orders_2(sK689,sK691,sK692) = iProver_top
    | r2_orders_2(sK689,sK690,sK691) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3652])).

cnf(c_173166,plain,
    ( r2_orders_2(sK689,sK691,sK690) = iProver_top
    | r2_orders_2(sK689,sK690,sK691) = iProver_top ),
    inference(demodulation,[status(thm)],[c_173142,c_107060])).

cnf(c_173175,plain,
    ( r2_orders_2(sK689,sK691,sK690) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_173165,c_173166])).

cnf(c_163815,plain,
    ( r2_orders_2(sK689,sK691,sK690) != iProver_top
    | m1_subset_1(sK691,u1_struct_0(sK689)) != iProver_top
    | m1_subset_1(sK690,u1_struct_0(sK689)) != iProver_top
    | v5_orders_2(sK689) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_163809,c_107063])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_173175,c_163815,c_3665,c_3664,c_3663,c_3662])).

%------------------------------------------------------------------------------
