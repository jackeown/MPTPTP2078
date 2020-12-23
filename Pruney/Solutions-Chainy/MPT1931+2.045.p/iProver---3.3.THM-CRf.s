%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:15 EST 2020

% Result     : Theorem 1.32s
% Output     : CNFRefutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 158 expanded)
%              Number of clauses        :   30 (  34 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  298 ( 754 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X3] :
                    ( ? [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ? [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        & r1_orders_2(X1,X5,X6)
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f28])).

fof(f31,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK2(X0,X1,X2,X5))
        & m1_subset_1(sK2(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK1(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK1(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK2(X0,X1,X2,X5))
                      & m1_subset_1(sK2(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f31,f30])).

fof(f47,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f4,f26])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_waybel_0(X0,sK4,u1_struct_0(X0))
        & l1_waybel_0(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK3,X1,u1_struct_0(sK3))
          & l1_waybel_0(X1,sK3)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3))
    & l1_waybel_0(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f35,f34])).

fof(f56,plain,(
    ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f41])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_220,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_221,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_220])).

cnf(c_1108,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_221])).

cnf(c_1433,plain,
    ( ~ r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k1_xboole_0,sK0(u1_struct_0(sK4)))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1108])).

cnf(c_9,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1088,plain,
    ( ~ r2_waybel_0(sK3,sK4,X0)
    | ~ l1_waybel_0(sK4,sK3)
    | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1213,plain,
    ( ~ r2_waybel_0(sK3,sK4,X0)
    | ~ l1_waybel_0(sK4,sK3)
    | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,X0,sK0(u1_struct_0(sK4)))),X0)
    | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1088])).

cnf(c_1432,plain,
    ( ~ r2_waybel_0(sK3,sK4,k1_xboole_0)
    | ~ l1_waybel_0(sK4,sK3)
    | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k1_xboole_0,sK0(u1_struct_0(sK4)))),k1_xboole_0)
    | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1213])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1156,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1109,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_12,plain,
    ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14,negated_conjecture,
    ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_286,plain,
    ( r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k6_subset_1(u1_struct_0(X0),X2) != u1_struct_0(sK3)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_287,plain,
    ( r2_waybel_0(sK3,sK4,X0)
    | ~ l1_waybel_0(sK4,sK3)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | k6_subset_1(u1_struct_0(sK3),X0) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_17,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_15,negated_conjecture,
    ( l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_291,plain,
    ( r2_waybel_0(sK3,sK4,X0)
    | k6_subset_1(u1_struct_0(sK3),X0) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_287,c_18,c_17,c_16,c_15])).

cnf(c_1097,plain,
    ( r2_waybel_0(sK3,sK4,k1_xboole_0)
    | k6_subset_1(u1_struct_0(sK3),k1_xboole_0) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_291])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k6_subset_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_213,plain,
    ( X0 != X1
    | k6_subset_1(X0,X2) = X0
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_214,plain,
    ( k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_1096,plain,
    ( k6_subset_1(u1_struct_0(sK3),k1_xboole_0) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1433,c_1432,c_1156,c_1109,c_1097,c_1096,c_15,c_16,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:40:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.32/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.32/0.98  
% 1.32/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.32/0.98  
% 1.32/0.98  ------  iProver source info
% 1.32/0.98  
% 1.32/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.32/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.32/0.98  git: non_committed_changes: false
% 1.32/0.98  git: last_make_outside_of_git: false
% 1.32/0.98  
% 1.32/0.98  ------ 
% 1.32/0.98  
% 1.32/0.98  ------ Input Options
% 1.32/0.98  
% 1.32/0.98  --out_options                           all
% 1.32/0.98  --tptp_safe_out                         true
% 1.32/0.98  --problem_path                          ""
% 1.32/0.98  --include_path                          ""
% 1.32/0.98  --clausifier                            res/vclausify_rel
% 1.32/0.98  --clausifier_options                    --mode clausify
% 1.32/0.98  --stdin                                 false
% 1.32/0.98  --stats_out                             all
% 1.32/0.98  
% 1.32/0.98  ------ General Options
% 1.32/0.98  
% 1.32/0.98  --fof                                   false
% 1.32/0.98  --time_out_real                         305.
% 1.32/0.98  --time_out_virtual                      -1.
% 1.32/0.98  --symbol_type_check                     false
% 1.32/0.98  --clausify_out                          false
% 1.32/0.98  --sig_cnt_out                           false
% 1.32/0.98  --trig_cnt_out                          false
% 1.32/0.98  --trig_cnt_out_tolerance                1.
% 1.32/0.98  --trig_cnt_out_sk_spl                   false
% 1.32/0.98  --abstr_cl_out                          false
% 1.32/0.98  
% 1.32/0.98  ------ Global Options
% 1.32/0.98  
% 1.32/0.98  --schedule                              default
% 1.32/0.98  --add_important_lit                     false
% 1.32/0.98  --prop_solver_per_cl                    1000
% 1.32/0.98  --min_unsat_core                        false
% 1.32/0.98  --soft_assumptions                      false
% 1.32/0.98  --soft_lemma_size                       3
% 1.32/0.98  --prop_impl_unit_size                   0
% 1.32/0.98  --prop_impl_unit                        []
% 1.32/0.98  --share_sel_clauses                     true
% 1.32/0.98  --reset_solvers                         false
% 1.32/0.98  --bc_imp_inh                            [conj_cone]
% 1.32/0.98  --conj_cone_tolerance                   3.
% 1.32/0.98  --extra_neg_conj                        none
% 1.32/0.98  --large_theory_mode                     true
% 1.32/0.98  --prolific_symb_bound                   200
% 1.32/0.98  --lt_threshold                          2000
% 1.32/0.98  --clause_weak_htbl                      true
% 1.32/0.98  --gc_record_bc_elim                     false
% 1.32/0.98  
% 1.32/0.98  ------ Preprocessing Options
% 1.32/0.98  
% 1.32/0.98  --preprocessing_flag                    true
% 1.32/0.98  --time_out_prep_mult                    0.1
% 1.32/0.98  --splitting_mode                        input
% 1.32/0.98  --splitting_grd                         true
% 1.32/0.98  --splitting_cvd                         false
% 1.32/0.98  --splitting_cvd_svl                     false
% 1.32/0.98  --splitting_nvd                         32
% 1.32/0.98  --sub_typing                            true
% 1.32/0.98  --prep_gs_sim                           true
% 1.32/0.98  --prep_unflatten                        true
% 1.32/0.98  --prep_res_sim                          true
% 1.32/0.98  --prep_upred                            true
% 1.32/0.98  --prep_sem_filter                       exhaustive
% 1.32/0.98  --prep_sem_filter_out                   false
% 1.32/0.98  --pred_elim                             true
% 1.32/0.98  --res_sim_input                         true
% 1.32/0.98  --eq_ax_congr_red                       true
% 1.32/0.98  --pure_diseq_elim                       true
% 1.32/0.98  --brand_transform                       false
% 1.32/0.98  --non_eq_to_eq                          false
% 1.32/0.98  --prep_def_merge                        true
% 1.32/0.98  --prep_def_merge_prop_impl              false
% 1.32/0.98  --prep_def_merge_mbd                    true
% 1.32/0.98  --prep_def_merge_tr_red                 false
% 1.32/0.98  --prep_def_merge_tr_cl                  false
% 1.32/0.98  --smt_preprocessing                     true
% 1.32/0.98  --smt_ac_axioms                         fast
% 1.32/0.98  --preprocessed_out                      false
% 1.32/0.98  --preprocessed_stats                    false
% 1.32/0.98  
% 1.32/0.98  ------ Abstraction refinement Options
% 1.32/0.98  
% 1.32/0.98  --abstr_ref                             []
% 1.32/0.98  --abstr_ref_prep                        false
% 1.32/0.98  --abstr_ref_until_sat                   false
% 1.32/0.98  --abstr_ref_sig_restrict                funpre
% 1.32/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.32/0.98  --abstr_ref_under                       []
% 1.32/0.98  
% 1.32/0.98  ------ SAT Options
% 1.32/0.98  
% 1.32/0.98  --sat_mode                              false
% 1.32/0.98  --sat_fm_restart_options                ""
% 1.32/0.98  --sat_gr_def                            false
% 1.32/0.98  --sat_epr_types                         true
% 1.32/0.98  --sat_non_cyclic_types                  false
% 1.32/0.98  --sat_finite_models                     false
% 1.32/0.98  --sat_fm_lemmas                         false
% 1.32/0.98  --sat_fm_prep                           false
% 1.32/0.98  --sat_fm_uc_incr                        true
% 1.32/0.98  --sat_out_model                         small
% 1.32/0.98  --sat_out_clauses                       false
% 1.32/0.98  
% 1.32/0.98  ------ QBF Options
% 1.32/0.98  
% 1.32/0.98  --qbf_mode                              false
% 1.32/0.98  --qbf_elim_univ                         false
% 1.32/0.98  --qbf_dom_inst                          none
% 1.32/0.98  --qbf_dom_pre_inst                      false
% 1.32/0.98  --qbf_sk_in                             false
% 1.32/0.98  --qbf_pred_elim                         true
% 1.32/0.98  --qbf_split                             512
% 1.32/0.98  
% 1.32/0.98  ------ BMC1 Options
% 1.32/0.98  
% 1.32/0.98  --bmc1_incremental                      false
% 1.32/0.98  --bmc1_axioms                           reachable_all
% 1.32/0.98  --bmc1_min_bound                        0
% 1.32/0.98  --bmc1_max_bound                        -1
% 1.32/0.98  --bmc1_max_bound_default                -1
% 1.32/0.98  --bmc1_symbol_reachability              true
% 1.32/0.98  --bmc1_property_lemmas                  false
% 1.32/0.98  --bmc1_k_induction                      false
% 1.32/0.98  --bmc1_non_equiv_states                 false
% 1.32/0.98  --bmc1_deadlock                         false
% 1.32/0.98  --bmc1_ucm                              false
% 1.32/0.98  --bmc1_add_unsat_core                   none
% 1.32/0.98  --bmc1_unsat_core_children              false
% 1.32/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.32/0.98  --bmc1_out_stat                         full
% 1.32/0.98  --bmc1_ground_init                      false
% 1.32/0.98  --bmc1_pre_inst_next_state              false
% 1.32/0.98  --bmc1_pre_inst_state                   false
% 1.32/0.98  --bmc1_pre_inst_reach_state             false
% 1.32/0.98  --bmc1_out_unsat_core                   false
% 1.32/0.98  --bmc1_aig_witness_out                  false
% 1.32/0.98  --bmc1_verbose                          false
% 1.32/0.98  --bmc1_dump_clauses_tptp                false
% 1.32/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.32/0.98  --bmc1_dump_file                        -
% 1.32/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.32/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.32/0.98  --bmc1_ucm_extend_mode                  1
% 1.32/0.98  --bmc1_ucm_init_mode                    2
% 1.32/0.98  --bmc1_ucm_cone_mode                    none
% 1.32/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.32/0.98  --bmc1_ucm_relax_model                  4
% 1.32/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.32/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.32/0.98  --bmc1_ucm_layered_model                none
% 1.32/0.98  --bmc1_ucm_max_lemma_size               10
% 1.32/0.98  
% 1.32/0.98  ------ AIG Options
% 1.32/0.98  
% 1.32/0.98  --aig_mode                              false
% 1.32/0.98  
% 1.32/0.98  ------ Instantiation Options
% 1.32/0.98  
% 1.32/0.98  --instantiation_flag                    true
% 1.32/0.98  --inst_sos_flag                         false
% 1.32/0.98  --inst_sos_phase                        true
% 1.32/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.32/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.32/0.98  --inst_lit_sel_side                     num_symb
% 1.32/0.98  --inst_solver_per_active                1400
% 1.32/0.98  --inst_solver_calls_frac                1.
% 1.32/0.98  --inst_passive_queue_type               priority_queues
% 1.32/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.32/0.98  --inst_passive_queues_freq              [25;2]
% 1.32/0.98  --inst_dismatching                      true
% 1.32/0.98  --inst_eager_unprocessed_to_passive     true
% 1.32/0.98  --inst_prop_sim_given                   true
% 1.32/0.98  --inst_prop_sim_new                     false
% 1.32/0.98  --inst_subs_new                         false
% 1.32/0.98  --inst_eq_res_simp                      false
% 1.32/0.98  --inst_subs_given                       false
% 1.32/0.98  --inst_orphan_elimination               true
% 1.32/0.98  --inst_learning_loop_flag               true
% 1.32/0.98  --inst_learning_start                   3000
% 1.32/0.98  --inst_learning_factor                  2
% 1.32/0.98  --inst_start_prop_sim_after_learn       3
% 1.32/0.98  --inst_sel_renew                        solver
% 1.32/0.98  --inst_lit_activity_flag                true
% 1.32/0.98  --inst_restr_to_given                   false
% 1.32/0.98  --inst_activity_threshold               500
% 1.32/0.98  --inst_out_proof                        true
% 1.32/0.98  
% 1.32/0.98  ------ Resolution Options
% 1.32/0.98  
% 1.32/0.98  --resolution_flag                       true
% 1.32/0.98  --res_lit_sel                           adaptive
% 1.32/0.98  --res_lit_sel_side                      none
% 1.32/0.98  --res_ordering                          kbo
% 1.32/0.98  --res_to_prop_solver                    active
% 1.32/0.98  --res_prop_simpl_new                    false
% 1.32/0.98  --res_prop_simpl_given                  true
% 1.32/0.98  --res_passive_queue_type                priority_queues
% 1.32/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.32/0.98  --res_passive_queues_freq               [15;5]
% 1.32/0.98  --res_forward_subs                      full
% 1.32/0.98  --res_backward_subs                     full
% 1.32/0.98  --res_forward_subs_resolution           true
% 1.32/0.98  --res_backward_subs_resolution          true
% 1.32/0.98  --res_orphan_elimination                true
% 1.32/0.98  --res_time_limit                        2.
% 1.32/0.98  --res_out_proof                         true
% 1.32/0.98  
% 1.32/0.98  ------ Superposition Options
% 1.32/0.98  
% 1.32/0.98  --superposition_flag                    true
% 1.32/0.98  --sup_passive_queue_type                priority_queues
% 1.32/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.32/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.32/0.98  --demod_completeness_check              fast
% 1.32/0.98  --demod_use_ground                      true
% 1.32/0.98  --sup_to_prop_solver                    passive
% 1.32/0.98  --sup_prop_simpl_new                    true
% 1.32/0.98  --sup_prop_simpl_given                  true
% 1.32/0.98  --sup_fun_splitting                     false
% 1.32/0.98  --sup_smt_interval                      50000
% 1.32/0.98  
% 1.32/0.98  ------ Superposition Simplification Setup
% 1.32/0.98  
% 1.32/0.98  --sup_indices_passive                   []
% 1.32/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.32/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/0.98  --sup_full_bw                           [BwDemod]
% 1.32/0.98  --sup_immed_triv                        [TrivRules]
% 1.32/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.32/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/0.98  --sup_immed_bw_main                     []
% 1.32/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.32/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.32/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.32/0.98  
% 1.32/0.98  ------ Combination Options
% 1.32/0.98  
% 1.32/0.98  --comb_res_mult                         3
% 1.32/0.98  --comb_sup_mult                         2
% 1.32/0.98  --comb_inst_mult                        10
% 1.32/0.98  
% 1.32/0.98  ------ Debug Options
% 1.32/0.98  
% 1.32/0.98  --dbg_backtrace                         false
% 1.32/0.98  --dbg_dump_prop_clauses                 false
% 1.32/0.98  --dbg_dump_prop_clauses_file            -
% 1.32/0.98  --dbg_out_stat                          false
% 1.32/0.98  ------ Parsing...
% 1.32/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.32/0.98  
% 1.32/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.32/0.98  
% 1.32/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.32/0.98  
% 1.32/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.32/0.98  ------ Proving...
% 1.32/0.98  ------ Problem Properties 
% 1.32/0.98  
% 1.32/0.98  
% 1.32/0.98  clauses                                 14
% 1.32/0.98  conjectures                             4
% 1.32/0.98  EPR                                     4
% 1.32/0.98  Horn                                    10
% 1.32/0.98  unary                                   7
% 1.32/0.98  binary                                  2
% 1.32/0.98  lits                                    44
% 1.32/0.98  lits eq                                 2
% 1.32/0.98  fd_pure                                 0
% 1.32/0.98  fd_pseudo                               0
% 1.32/0.98  fd_cond                                 0
% 1.32/0.98  fd_pseudo_cond                          0
% 1.32/0.98  AC symbols                              0
% 1.32/0.98  
% 1.32/0.98  ------ Schedule dynamic 5 is on 
% 1.32/0.98  
% 1.32/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.32/0.98  
% 1.32/0.98  
% 1.32/0.98  ------ 
% 1.32/0.98  Current options:
% 1.32/0.98  ------ 
% 1.32/0.98  
% 1.32/0.98  ------ Input Options
% 1.32/0.98  
% 1.32/0.98  --out_options                           all
% 1.32/0.98  --tptp_safe_out                         true
% 1.32/0.98  --problem_path                          ""
% 1.32/0.98  --include_path                          ""
% 1.32/0.98  --clausifier                            res/vclausify_rel
% 1.32/0.98  --clausifier_options                    --mode clausify
% 1.32/0.98  --stdin                                 false
% 1.32/0.98  --stats_out                             all
% 1.32/0.99  
% 1.32/0.99  ------ General Options
% 1.32/0.99  
% 1.32/0.99  --fof                                   false
% 1.32/0.99  --time_out_real                         305.
% 1.32/0.99  --time_out_virtual                      -1.
% 1.32/0.99  --symbol_type_check                     false
% 1.32/0.99  --clausify_out                          false
% 1.32/0.99  --sig_cnt_out                           false
% 1.32/0.99  --trig_cnt_out                          false
% 1.32/0.99  --trig_cnt_out_tolerance                1.
% 1.32/0.99  --trig_cnt_out_sk_spl                   false
% 1.32/0.99  --abstr_cl_out                          false
% 1.32/0.99  
% 1.32/0.99  ------ Global Options
% 1.32/0.99  
% 1.32/0.99  --schedule                              default
% 1.32/0.99  --add_important_lit                     false
% 1.32/0.99  --prop_solver_per_cl                    1000
% 1.32/0.99  --min_unsat_core                        false
% 1.32/0.99  --soft_assumptions                      false
% 1.32/0.99  --soft_lemma_size                       3
% 1.32/0.99  --prop_impl_unit_size                   0
% 1.32/0.99  --prop_impl_unit                        []
% 1.32/0.99  --share_sel_clauses                     true
% 1.32/0.99  --reset_solvers                         false
% 1.32/0.99  --bc_imp_inh                            [conj_cone]
% 1.32/0.99  --conj_cone_tolerance                   3.
% 1.32/0.99  --extra_neg_conj                        none
% 1.32/0.99  --large_theory_mode                     true
% 1.32/0.99  --prolific_symb_bound                   200
% 1.32/0.99  --lt_threshold                          2000
% 1.32/0.99  --clause_weak_htbl                      true
% 1.32/0.99  --gc_record_bc_elim                     false
% 1.32/0.99  
% 1.32/0.99  ------ Preprocessing Options
% 1.32/0.99  
% 1.32/0.99  --preprocessing_flag                    true
% 1.32/0.99  --time_out_prep_mult                    0.1
% 1.32/0.99  --splitting_mode                        input
% 1.32/0.99  --splitting_grd                         true
% 1.32/0.99  --splitting_cvd                         false
% 1.32/0.99  --splitting_cvd_svl                     false
% 1.32/0.99  --splitting_nvd                         32
% 1.32/0.99  --sub_typing                            true
% 1.32/0.99  --prep_gs_sim                           true
% 1.32/0.99  --prep_unflatten                        true
% 1.32/0.99  --prep_res_sim                          true
% 1.32/0.99  --prep_upred                            true
% 1.32/0.99  --prep_sem_filter                       exhaustive
% 1.32/0.99  --prep_sem_filter_out                   false
% 1.32/0.99  --pred_elim                             true
% 1.32/0.99  --res_sim_input                         true
% 1.32/0.99  --eq_ax_congr_red                       true
% 1.32/0.99  --pure_diseq_elim                       true
% 1.32/0.99  --brand_transform                       false
% 1.32/0.99  --non_eq_to_eq                          false
% 1.32/0.99  --prep_def_merge                        true
% 1.32/0.99  --prep_def_merge_prop_impl              false
% 1.32/0.99  --prep_def_merge_mbd                    true
% 1.32/0.99  --prep_def_merge_tr_red                 false
% 1.32/0.99  --prep_def_merge_tr_cl                  false
% 1.32/0.99  --smt_preprocessing                     true
% 1.32/0.99  --smt_ac_axioms                         fast
% 1.32/0.99  --preprocessed_out                      false
% 1.32/0.99  --preprocessed_stats                    false
% 1.32/0.99  
% 1.32/0.99  ------ Abstraction refinement Options
% 1.32/0.99  
% 1.32/0.99  --abstr_ref                             []
% 1.32/0.99  --abstr_ref_prep                        false
% 1.32/0.99  --abstr_ref_until_sat                   false
% 1.32/0.99  --abstr_ref_sig_restrict                funpre
% 1.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.32/0.99  --abstr_ref_under                       []
% 1.32/0.99  
% 1.32/0.99  ------ SAT Options
% 1.32/0.99  
% 1.32/0.99  --sat_mode                              false
% 1.32/0.99  --sat_fm_restart_options                ""
% 1.32/0.99  --sat_gr_def                            false
% 1.32/0.99  --sat_epr_types                         true
% 1.32/0.99  --sat_non_cyclic_types                  false
% 1.32/0.99  --sat_finite_models                     false
% 1.32/0.99  --sat_fm_lemmas                         false
% 1.32/0.99  --sat_fm_prep                           false
% 1.32/0.99  --sat_fm_uc_incr                        true
% 1.32/0.99  --sat_out_model                         small
% 1.32/0.99  --sat_out_clauses                       false
% 1.32/0.99  
% 1.32/0.99  ------ QBF Options
% 1.32/0.99  
% 1.32/0.99  --qbf_mode                              false
% 1.32/0.99  --qbf_elim_univ                         false
% 1.32/0.99  --qbf_dom_inst                          none
% 1.32/0.99  --qbf_dom_pre_inst                      false
% 1.32/0.99  --qbf_sk_in                             false
% 1.32/0.99  --qbf_pred_elim                         true
% 1.32/0.99  --qbf_split                             512
% 1.32/0.99  
% 1.32/0.99  ------ BMC1 Options
% 1.32/0.99  
% 1.32/0.99  --bmc1_incremental                      false
% 1.32/0.99  --bmc1_axioms                           reachable_all
% 1.32/0.99  --bmc1_min_bound                        0
% 1.32/0.99  --bmc1_max_bound                        -1
% 1.32/0.99  --bmc1_max_bound_default                -1
% 1.32/0.99  --bmc1_symbol_reachability              true
% 1.32/0.99  --bmc1_property_lemmas                  false
% 1.32/0.99  --bmc1_k_induction                      false
% 1.32/0.99  --bmc1_non_equiv_states                 false
% 1.32/0.99  --bmc1_deadlock                         false
% 1.32/0.99  --bmc1_ucm                              false
% 1.32/0.99  --bmc1_add_unsat_core                   none
% 1.32/0.99  --bmc1_unsat_core_children              false
% 1.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.32/0.99  --bmc1_out_stat                         full
% 1.32/0.99  --bmc1_ground_init                      false
% 1.32/0.99  --bmc1_pre_inst_next_state              false
% 1.32/0.99  --bmc1_pre_inst_state                   false
% 1.32/0.99  --bmc1_pre_inst_reach_state             false
% 1.32/0.99  --bmc1_out_unsat_core                   false
% 1.32/0.99  --bmc1_aig_witness_out                  false
% 1.32/0.99  --bmc1_verbose                          false
% 1.32/0.99  --bmc1_dump_clauses_tptp                false
% 1.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.32/0.99  --bmc1_dump_file                        -
% 1.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.32/0.99  --bmc1_ucm_extend_mode                  1
% 1.32/0.99  --bmc1_ucm_init_mode                    2
% 1.32/0.99  --bmc1_ucm_cone_mode                    none
% 1.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.32/0.99  --bmc1_ucm_relax_model                  4
% 1.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.32/0.99  --bmc1_ucm_layered_model                none
% 1.32/0.99  --bmc1_ucm_max_lemma_size               10
% 1.32/0.99  
% 1.32/0.99  ------ AIG Options
% 1.32/0.99  
% 1.32/0.99  --aig_mode                              false
% 1.32/0.99  
% 1.32/0.99  ------ Instantiation Options
% 1.32/0.99  
% 1.32/0.99  --instantiation_flag                    true
% 1.32/0.99  --inst_sos_flag                         false
% 1.32/0.99  --inst_sos_phase                        true
% 1.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.32/0.99  --inst_lit_sel_side                     none
% 1.32/0.99  --inst_solver_per_active                1400
% 1.32/0.99  --inst_solver_calls_frac                1.
% 1.32/0.99  --inst_passive_queue_type               priority_queues
% 1.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.32/0.99  --inst_passive_queues_freq              [25;2]
% 1.32/0.99  --inst_dismatching                      true
% 1.32/0.99  --inst_eager_unprocessed_to_passive     true
% 1.32/0.99  --inst_prop_sim_given                   true
% 1.32/0.99  --inst_prop_sim_new                     false
% 1.32/0.99  --inst_subs_new                         false
% 1.32/0.99  --inst_eq_res_simp                      false
% 1.32/0.99  --inst_subs_given                       false
% 1.32/0.99  --inst_orphan_elimination               true
% 1.32/0.99  --inst_learning_loop_flag               true
% 1.32/0.99  --inst_learning_start                   3000
% 1.32/0.99  --inst_learning_factor                  2
% 1.32/0.99  --inst_start_prop_sim_after_learn       3
% 1.32/0.99  --inst_sel_renew                        solver
% 1.32/0.99  --inst_lit_activity_flag                true
% 1.32/0.99  --inst_restr_to_given                   false
% 1.32/0.99  --inst_activity_threshold               500
% 1.32/0.99  --inst_out_proof                        true
% 1.32/0.99  
% 1.32/0.99  ------ Resolution Options
% 1.32/0.99  
% 1.32/0.99  --resolution_flag                       false
% 1.32/0.99  --res_lit_sel                           adaptive
% 1.32/0.99  --res_lit_sel_side                      none
% 1.32/0.99  --res_ordering                          kbo
% 1.32/0.99  --res_to_prop_solver                    active
% 1.32/0.99  --res_prop_simpl_new                    false
% 1.32/0.99  --res_prop_simpl_given                  true
% 1.32/0.99  --res_passive_queue_type                priority_queues
% 1.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.32/0.99  --res_passive_queues_freq               [15;5]
% 1.32/0.99  --res_forward_subs                      full
% 1.32/0.99  --res_backward_subs                     full
% 1.32/0.99  --res_forward_subs_resolution           true
% 1.32/0.99  --res_backward_subs_resolution          true
% 1.32/0.99  --res_orphan_elimination                true
% 1.32/0.99  --res_time_limit                        2.
% 1.32/0.99  --res_out_proof                         true
% 1.32/0.99  
% 1.32/0.99  ------ Superposition Options
% 1.32/0.99  
% 1.32/0.99  --superposition_flag                    true
% 1.32/0.99  --sup_passive_queue_type                priority_queues
% 1.32/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.32/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.32/0.99  --demod_completeness_check              fast
% 1.32/0.99  --demod_use_ground                      true
% 1.32/0.99  --sup_to_prop_solver                    passive
% 1.32/0.99  --sup_prop_simpl_new                    true
% 1.32/0.99  --sup_prop_simpl_given                  true
% 1.32/0.99  --sup_fun_splitting                     false
% 1.32/0.99  --sup_smt_interval                      50000
% 1.32/0.99  
% 1.32/0.99  ------ Superposition Simplification Setup
% 1.32/0.99  
% 1.32/0.99  --sup_indices_passive                   []
% 1.32/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.32/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/0.99  --sup_full_bw                           [BwDemod]
% 1.32/0.99  --sup_immed_triv                        [TrivRules]
% 1.32/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.32/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/0.99  --sup_immed_bw_main                     []
% 1.32/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.32/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.32/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.32/0.99  
% 1.32/0.99  ------ Combination Options
% 1.32/0.99  
% 1.32/0.99  --comb_res_mult                         3
% 1.32/0.99  --comb_sup_mult                         2
% 1.32/0.99  --comb_inst_mult                        10
% 1.32/0.99  
% 1.32/0.99  ------ Debug Options
% 1.32/0.99  
% 1.32/0.99  --dbg_backtrace                         false
% 1.32/0.99  --dbg_dump_prop_clauses                 false
% 1.32/0.99  --dbg_dump_prop_clauses_file            -
% 1.32/0.99  --dbg_out_stat                          false
% 1.32/0.99  
% 1.32/0.99  
% 1.32/0.99  
% 1.32/0.99  
% 1.32/0.99  ------ Proving...
% 1.32/0.99  
% 1.32/0.99  
% 1.32/0.99  % SZS status Theorem for theBenchmark.p
% 1.32/0.99  
% 1.32/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.32/0.99  
% 1.32/0.99  fof(f1,axiom,(
% 1.32/0.99    v1_xboole_0(k1_xboole_0)),
% 1.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/0.99  
% 1.32/0.99  fof(f37,plain,(
% 1.32/0.99    v1_xboole_0(k1_xboole_0)),
% 1.32/0.99    inference(cnf_transformation,[],[f1])).
% 1.32/0.99  
% 1.32/0.99  fof(f8,axiom,(
% 1.32/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/0.99  
% 1.32/0.99  fof(f19,plain,(
% 1.32/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.32/0.99    inference(ennf_transformation,[],[f8])).
% 1.32/0.99  
% 1.32/0.99  fof(f44,plain,(
% 1.32/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.32/0.99    inference(cnf_transformation,[],[f19])).
% 1.32/0.99  
% 1.32/0.99  fof(f9,axiom,(
% 1.32/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 1.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/0.99  
% 1.32/0.99  fof(f20,plain,(
% 1.32/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.32/0.99    inference(ennf_transformation,[],[f9])).
% 1.32/0.99  
% 1.32/0.99  fof(f21,plain,(
% 1.32/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.32/0.99    inference(flattening,[],[f20])).
% 1.32/0.99  
% 1.32/0.99  fof(f28,plain,(
% 1.32/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.32/0.99    inference(nnf_transformation,[],[f21])).
% 1.32/0.99  
% 1.32/0.99  fof(f29,plain,(
% 1.32/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.32/0.99    inference(rectify,[],[f28])).
% 1.32/0.99  
% 1.32/0.99  fof(f31,plain,(
% 1.32/0.99    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK2(X0,X1,X2,X5)) & m1_subset_1(sK2(X0,X1,X2,X5),u1_struct_0(X1))))),
% 1.32/0.99    introduced(choice_axiom,[])).
% 1.32/0.99  
% 1.32/0.99  fof(f30,plain,(
% 1.32/0.99    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK1(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))))),
% 1.32/0.99    introduced(choice_axiom,[])).
% 1.32/0.99  
% 1.32/0.99  fof(f32,plain,(
% 1.32/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK1(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK2(X0,X1,X2,X5)) & m1_subset_1(sK2(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f31,f30])).
% 1.32/0.99  
% 1.32/0.99  fof(f47,plain,(
% 1.32/0.99    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.32/0.99    inference(cnf_transformation,[],[f32])).
% 1.32/0.99  
% 1.32/0.99  fof(f4,axiom,(
% 1.32/0.99    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/0.99  
% 1.32/0.99  fof(f26,plain,(
% 1.32/0.99    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 1.32/0.99    introduced(choice_axiom,[])).
% 1.32/0.99  
% 1.32/0.99  fof(f27,plain,(
% 1.32/0.99    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 1.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f4,f26])).
% 1.32/0.99  
% 1.32/0.99  fof(f40,plain,(
% 1.32/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 1.32/0.99    inference(cnf_transformation,[],[f27])).
% 1.32/0.99  
% 1.32/0.99  fof(f6,axiom,(
% 1.32/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/0.99  
% 1.32/0.99  fof(f42,plain,(
% 1.32/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.32/0.99    inference(cnf_transformation,[],[f6])).
% 1.32/0.99  
% 1.32/0.99  fof(f10,axiom,(
% 1.32/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 1.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/0.99  
% 1.32/0.99  fof(f22,plain,(
% 1.32/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.32/0.99    inference(ennf_transformation,[],[f10])).
% 1.32/0.99  
% 1.32/0.99  fof(f23,plain,(
% 1.32/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.32/0.99    inference(flattening,[],[f22])).
% 1.32/0.99  
% 1.32/0.99  fof(f33,plain,(
% 1.32/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.32/0.99    inference(nnf_transformation,[],[f23])).
% 1.32/0.99  
% 1.32/0.99  fof(f51,plain,(
% 1.32/0.99    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.32/0.99    inference(cnf_transformation,[],[f33])).
% 1.32/0.99  
% 1.32/0.99  fof(f11,conjecture,(
% 1.32/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/0.99  
% 1.32/0.99  fof(f12,negated_conjecture,(
% 1.32/0.99    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.32/0.99    inference(negated_conjecture,[],[f11])).
% 1.32/0.99  
% 1.32/0.99  fof(f14,plain,(
% 1.32/0.99    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.32/0.99    inference(pure_predicate_removal,[],[f12])).
% 1.32/0.99  
% 1.32/0.99  fof(f15,plain,(
% 1.32/0.99    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.32/0.99    inference(pure_predicate_removal,[],[f14])).
% 1.32/0.99  
% 1.32/0.99  fof(f24,plain,(
% 1.32/0.99    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.32/0.99    inference(ennf_transformation,[],[f15])).
% 1.32/0.99  
% 1.32/0.99  fof(f25,plain,(
% 1.32/0.99    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.32/0.99    inference(flattening,[],[f24])).
% 1.32/0.99  
% 1.32/0.99  fof(f35,plain,(
% 1.32/0.99    ( ! [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (~r1_waybel_0(X0,sK4,u1_struct_0(X0)) & l1_waybel_0(sK4,X0) & ~v2_struct_0(sK4))) )),
% 1.32/0.99    introduced(choice_axiom,[])).
% 1.32/0.99  
% 1.32/0.99  fof(f34,plain,(
% 1.32/0.99    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK3,X1,u1_struct_0(sK3)) & l1_waybel_0(X1,sK3) & ~v2_struct_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 1.32/0.99    introduced(choice_axiom,[])).
% 1.32/0.99  
% 1.32/0.99  fof(f36,plain,(
% 1.32/0.99    (~r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) & l1_waybel_0(sK4,sK3) & ~v2_struct_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 1.32/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f35,f34])).
% 1.32/0.99  
% 1.32/0.99  fof(f56,plain,(
% 1.32/0.99    ~r1_waybel_0(sK3,sK4,u1_struct_0(sK3))),
% 1.32/0.99    inference(cnf_transformation,[],[f36])).
% 1.32/0.99  
% 1.32/0.99  fof(f52,plain,(
% 1.32/0.99    ~v2_struct_0(sK3)),
% 1.32/0.99    inference(cnf_transformation,[],[f36])).
% 1.32/0.99  
% 1.32/0.99  fof(f53,plain,(
% 1.32/0.99    l1_struct_0(sK3)),
% 1.32/0.99    inference(cnf_transformation,[],[f36])).
% 1.32/0.99  
% 1.32/0.99  fof(f54,plain,(
% 1.32/0.99    ~v2_struct_0(sK4)),
% 1.32/0.99    inference(cnf_transformation,[],[f36])).
% 1.32/0.99  
% 1.32/0.99  fof(f55,plain,(
% 1.32/0.99    l1_waybel_0(sK4,sK3)),
% 1.32/0.99    inference(cnf_transformation,[],[f36])).
% 1.32/0.99  
% 1.32/0.99  fof(f2,axiom,(
% 1.32/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/0.99  
% 1.32/0.99  fof(f38,plain,(
% 1.32/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.32/0.99    inference(cnf_transformation,[],[f2])).
% 1.32/0.99  
% 1.32/0.99  fof(f3,axiom,(
% 1.32/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/0.99  
% 1.32/0.99  fof(f13,plain,(
% 1.32/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 1.32/0.99    inference(unused_predicate_definition_removal,[],[f3])).
% 1.32/0.99  
% 1.32/0.99  fof(f16,plain,(
% 1.32/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.32/0.99    inference(ennf_transformation,[],[f13])).
% 1.32/0.99  
% 1.32/0.99  fof(f39,plain,(
% 1.32/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.32/0.99    inference(cnf_transformation,[],[f16])).
% 1.32/0.99  
% 1.32/0.99  fof(f5,axiom,(
% 1.32/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.32/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/0.99  
% 1.32/0.99  fof(f41,plain,(
% 1.32/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.32/0.99    inference(cnf_transformation,[],[f5])).
% 1.32/0.99  
% 1.32/0.99  fof(f57,plain,(
% 1.32/0.99    ( ! [X0,X1] : (k6_subset_1(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.32/0.99    inference(definition_unfolding,[],[f39,f41])).
% 1.32/0.99  
% 1.32/0.99  cnf(c_0,plain,
% 1.32/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 1.32/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_6,plain,
% 1.32/0.99      ( ~ r2_hidden(X0,X1)
% 1.32/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.32/0.99      | ~ v1_xboole_0(X2) ),
% 1.32/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_220,plain,
% 1.32/0.99      ( ~ r2_hidden(X0,X1)
% 1.32/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.32/0.99      | k1_xboole_0 != X2 ),
% 1.32/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_221,plain,
% 1.32/0.99      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
% 1.32/0.99      inference(unflattening,[status(thm)],[c_220]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_1108,plain,
% 1.32/0.99      ( ~ r2_hidden(X0,k1_xboole_0)
% 1.32/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 1.32/0.99      inference(instantiation,[status(thm)],[c_221]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_1433,plain,
% 1.32/0.99      ( ~ r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k1_xboole_0,sK0(u1_struct_0(sK4)))),k1_xboole_0)
% 1.32/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 1.32/0.99      inference(instantiation,[status(thm)],[c_1108]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_9,plain,
% 1.32/0.99      ( ~ r2_waybel_0(X0,X1,X2)
% 1.32/0.99      | ~ l1_waybel_0(X1,X0)
% 1.32/0.99      | r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
% 1.32/0.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.32/0.99      | ~ l1_struct_0(X0)
% 1.32/0.99      | v2_struct_0(X0)
% 1.32/0.99      | v2_struct_0(X1) ),
% 1.32/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_1088,plain,
% 1.32/0.99      ( ~ r2_waybel_0(sK3,sK4,X0)
% 1.32/0.99      | ~ l1_waybel_0(sK4,sK3)
% 1.32/0.99      | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,X0,X1)),X0)
% 1.32/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.32/0.99      | ~ l1_struct_0(sK3)
% 1.32/0.99      | v2_struct_0(sK4)
% 1.32/0.99      | v2_struct_0(sK3) ),
% 1.32/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_1213,plain,
% 1.32/0.99      ( ~ r2_waybel_0(sK3,sK4,X0)
% 1.32/0.99      | ~ l1_waybel_0(sK4,sK3)
% 1.32/0.99      | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,X0,sK0(u1_struct_0(sK4)))),X0)
% 1.32/0.99      | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
% 1.32/0.99      | ~ l1_struct_0(sK3)
% 1.32/0.99      | v2_struct_0(sK4)
% 1.32/0.99      | v2_struct_0(sK3) ),
% 1.32/0.99      inference(instantiation,[status(thm)],[c_1088]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_1432,plain,
% 1.32/0.99      ( ~ r2_waybel_0(sK3,sK4,k1_xboole_0)
% 1.32/0.99      | ~ l1_waybel_0(sK4,sK3)
% 1.32/0.99      | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k1_xboole_0,sK0(u1_struct_0(sK4)))),k1_xboole_0)
% 1.32/0.99      | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
% 1.32/0.99      | ~ l1_struct_0(sK3)
% 1.32/0.99      | v2_struct_0(sK4)
% 1.32/0.99      | v2_struct_0(sK3) ),
% 1.32/0.99      inference(instantiation,[status(thm)],[c_1213]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_3,plain,
% 1.32/0.99      ( m1_subset_1(sK0(X0),X0) ),
% 1.32/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_1156,plain,
% 1.32/0.99      ( m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) ),
% 1.32/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_4,plain,
% 1.32/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.32/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_1109,plain,
% 1.32/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 1.32/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_12,plain,
% 1.32/0.99      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 1.32/0.99      | r2_waybel_0(X0,X1,X2)
% 1.32/0.99      | ~ l1_waybel_0(X1,X0)
% 1.32/0.99      | ~ l1_struct_0(X0)
% 1.32/0.99      | v2_struct_0(X0)
% 1.32/0.99      | v2_struct_0(X1) ),
% 1.32/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_14,negated_conjecture,
% 1.32/0.99      ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) ),
% 1.32/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_286,plain,
% 1.32/0.99      ( r2_waybel_0(X0,X1,X2)
% 1.32/0.99      | ~ l1_waybel_0(X1,X0)
% 1.32/0.99      | ~ l1_struct_0(X0)
% 1.32/0.99      | v2_struct_0(X0)
% 1.32/0.99      | v2_struct_0(X1)
% 1.32/0.99      | k6_subset_1(u1_struct_0(X0),X2) != u1_struct_0(sK3)
% 1.32/0.99      | sK4 != X1
% 1.32/0.99      | sK3 != X0 ),
% 1.32/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_287,plain,
% 1.32/0.99      ( r2_waybel_0(sK3,sK4,X0)
% 1.32/0.99      | ~ l1_waybel_0(sK4,sK3)
% 1.32/0.99      | ~ l1_struct_0(sK3)
% 1.32/0.99      | v2_struct_0(sK4)
% 1.32/0.99      | v2_struct_0(sK3)
% 1.32/0.99      | k6_subset_1(u1_struct_0(sK3),X0) != u1_struct_0(sK3) ),
% 1.32/0.99      inference(unflattening,[status(thm)],[c_286]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_18,negated_conjecture,
% 1.32/0.99      ( ~ v2_struct_0(sK3) ),
% 1.32/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_17,negated_conjecture,
% 1.32/0.99      ( l1_struct_0(sK3) ),
% 1.32/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_16,negated_conjecture,
% 1.32/0.99      ( ~ v2_struct_0(sK4) ),
% 1.32/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_15,negated_conjecture,
% 1.32/0.99      ( l1_waybel_0(sK4,sK3) ),
% 1.32/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_291,plain,
% 1.32/0.99      ( r2_waybel_0(sK3,sK4,X0)
% 1.32/0.99      | k6_subset_1(u1_struct_0(sK3),X0) != u1_struct_0(sK3) ),
% 1.32/0.99      inference(global_propositional_subsumption,
% 1.32/0.99                [status(thm)],
% 1.32/0.99                [c_287,c_18,c_17,c_16,c_15]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_1097,plain,
% 1.32/0.99      ( r2_waybel_0(sK3,sK4,k1_xboole_0)
% 1.32/0.99      | k6_subset_1(u1_struct_0(sK3),k1_xboole_0) != u1_struct_0(sK3) ),
% 1.32/0.99      inference(instantiation,[status(thm)],[c_291]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_1,plain,
% 1.32/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 1.32/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_2,plain,
% 1.32/0.99      ( ~ r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) = X0 ),
% 1.32/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_213,plain,
% 1.32/0.99      ( X0 != X1 | k6_subset_1(X0,X2) = X0 | k1_xboole_0 != X2 ),
% 1.32/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_214,plain,
% 1.32/0.99      ( k6_subset_1(X0,k1_xboole_0) = X0 ),
% 1.32/0.99      inference(unflattening,[status(thm)],[c_213]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(c_1096,plain,
% 1.32/0.99      ( k6_subset_1(u1_struct_0(sK3),k1_xboole_0) = u1_struct_0(sK3) ),
% 1.32/0.99      inference(instantiation,[status(thm)],[c_214]) ).
% 1.32/0.99  
% 1.32/0.99  cnf(contradiction,plain,
% 1.32/0.99      ( $false ),
% 1.32/0.99      inference(minisat,
% 1.32/0.99                [status(thm)],
% 1.32/0.99                [c_1433,c_1432,c_1156,c_1109,c_1097,c_1096,c_15,c_16,
% 1.32/0.99                 c_17,c_18]) ).
% 1.32/0.99  
% 1.32/0.99  
% 1.32/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.32/0.99  
% 1.32/0.99  ------                               Statistics
% 1.32/0.99  
% 1.32/0.99  ------ General
% 1.32/0.99  
% 1.32/0.99  abstr_ref_over_cycles:                  0
% 1.32/0.99  abstr_ref_under_cycles:                 0
% 1.32/0.99  gc_basic_clause_elim:                   0
% 1.32/0.99  forced_gc_time:                         0
% 1.32/0.99  parsing_time:                           0.01
% 1.32/0.99  unif_index_cands_time:                  0.
% 1.32/0.99  unif_index_add_time:                    0.
% 1.32/0.99  orderings_time:                         0.
% 1.32/0.99  out_proof_time:                         0.008
% 1.32/0.99  total_time:                             0.081
% 1.32/0.99  num_of_symbols:                         51
% 1.32/0.99  num_of_terms:                           1381
% 1.32/0.99  
% 1.32/0.99  ------ Preprocessing
% 1.32/0.99  
% 1.32/0.99  num_of_splits:                          0
% 1.32/0.99  num_of_split_atoms:                     0
% 1.32/0.99  num_of_reused_defs:                     0
% 1.32/0.99  num_eq_ax_congr_red:                    40
% 1.32/0.99  num_of_sem_filtered_clauses:            1
% 1.32/0.99  num_of_subtypes:                        0
% 1.32/0.99  monotx_restored_types:                  0
% 1.32/0.99  sat_num_of_epr_types:                   0
% 1.32/0.99  sat_num_of_non_cyclic_types:            0
% 1.32/0.99  sat_guarded_non_collapsed_types:        0
% 1.32/0.99  num_pure_diseq_elim:                    0
% 1.32/0.99  simp_replaced_by:                       0
% 1.32/0.99  res_preprocessed:                       88
% 1.32/0.99  prep_upred:                             0
% 1.32/0.99  prep_unflattend:                        18
% 1.32/0.99  smt_new_axioms:                         0
% 1.32/0.99  pred_elim_cands:                        6
% 1.32/0.99  pred_elim:                              4
% 1.32/0.99  pred_elim_cl:                           5
% 1.32/0.99  pred_elim_cycles:                       6
% 1.32/0.99  merged_defs:                            0
% 1.32/0.99  merged_defs_ncl:                        0
% 1.32/0.99  bin_hyper_res:                          0
% 1.32/0.99  prep_cycles:                            4
% 1.32/0.99  pred_elim_time:                         0.007
% 1.32/0.99  splitting_time:                         0.
% 1.32/0.99  sem_filter_time:                        0.
% 1.32/0.99  monotx_time:                            0.001
% 1.32/0.99  subtype_inf_time:                       0.
% 1.32/0.99  
% 1.32/0.99  ------ Problem properties
% 1.32/0.99  
% 1.32/0.99  clauses:                                14
% 1.32/0.99  conjectures:                            4
% 1.32/0.99  epr:                                    4
% 1.32/0.99  horn:                                   10
% 1.32/0.99  ground:                                 4
% 1.32/0.99  unary:                                  7
% 1.32/0.99  binary:                                 2
% 1.32/0.99  lits:                                   44
% 1.32/0.99  lits_eq:                                2
% 1.32/0.99  fd_pure:                                0
% 1.32/0.99  fd_pseudo:                              0
% 1.32/0.99  fd_cond:                                0
% 1.32/0.99  fd_pseudo_cond:                         0
% 1.32/0.99  ac_symbols:                             0
% 1.32/0.99  
% 1.32/0.99  ------ Propositional Solver
% 1.32/0.99  
% 1.32/0.99  prop_solver_calls:                      24
% 1.32/0.99  prop_fast_solver_calls:                 652
% 1.32/0.99  smt_solver_calls:                       0
% 1.32/0.99  smt_fast_solver_calls:                  0
% 1.32/0.99  prop_num_of_clauses:                    337
% 1.32/0.99  prop_preprocess_simplified:             2489
% 1.32/0.99  prop_fo_subsumed:                       4
% 1.32/0.99  prop_solver_time:                       0.
% 1.32/0.99  smt_solver_time:                        0.
% 1.32/0.99  smt_fast_solver_time:                   0.
% 1.32/0.99  prop_fast_solver_time:                  0.
% 1.32/0.99  prop_unsat_core_time:                   0.
% 1.32/0.99  
% 1.32/0.99  ------ QBF
% 1.32/0.99  
% 1.32/0.99  qbf_q_res:                              0
% 1.32/0.99  qbf_num_tautologies:                    0
% 1.32/0.99  qbf_prep_cycles:                        0
% 1.32/0.99  
% 1.32/0.99  ------ BMC1
% 1.32/0.99  
% 1.32/0.99  bmc1_current_bound:                     -1
% 1.32/0.99  bmc1_last_solved_bound:                 -1
% 1.32/0.99  bmc1_unsat_core_size:                   -1
% 1.32/0.99  bmc1_unsat_core_parents_size:           -1
% 1.32/0.99  bmc1_merge_next_fun:                    0
% 1.32/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.32/0.99  
% 1.32/0.99  ------ Instantiation
% 1.32/0.99  
% 1.32/0.99  inst_num_of_clauses:                    107
% 1.32/0.99  inst_num_in_passive:                    42
% 1.32/0.99  inst_num_in_active:                     59
% 1.32/0.99  inst_num_in_unprocessed:                5
% 1.32/0.99  inst_num_of_loops:                      65
% 1.32/0.99  inst_num_of_learning_restarts:          0
% 1.32/0.99  inst_num_moves_active_passive:          3
% 1.32/0.99  inst_lit_activity:                      0
% 1.32/0.99  inst_lit_activity_moves:                0
% 1.32/0.99  inst_num_tautologies:                   0
% 1.32/0.99  inst_num_prop_implied:                  0
% 1.32/0.99  inst_num_existing_simplified:           0
% 1.32/0.99  inst_num_eq_res_simplified:             0
% 1.32/0.99  inst_num_child_elim:                    0
% 1.32/0.99  inst_num_of_dismatching_blockings:      5
% 1.32/0.99  inst_num_of_non_proper_insts:           51
% 1.32/0.99  inst_num_of_duplicates:                 0
% 1.32/0.99  inst_inst_num_from_inst_to_res:         0
% 1.32/0.99  inst_dismatching_checking_time:         0.
% 1.32/0.99  
% 1.32/0.99  ------ Resolution
% 1.32/0.99  
% 1.32/0.99  res_num_of_clauses:                     0
% 1.32/0.99  res_num_in_passive:                     0
% 1.32/0.99  res_num_in_active:                      0
% 1.32/0.99  res_num_of_loops:                       92
% 1.32/0.99  res_forward_subset_subsumed:            3
% 1.32/0.99  res_backward_subset_subsumed:           0
% 1.32/0.99  res_forward_subsumed:                   0
% 1.32/0.99  res_backward_subsumed:                  0
% 1.32/0.99  res_forward_subsumption_resolution:     2
% 1.32/0.99  res_backward_subsumption_resolution:    0
% 1.32/0.99  res_clause_to_clause_subsumption:       19
% 1.32/0.99  res_orphan_elimination:                 0
% 1.32/0.99  res_tautology_del:                      6
% 1.32/0.99  res_num_eq_res_simplified:              0
% 1.32/0.99  res_num_sel_changes:                    0
% 1.32/0.99  res_moves_from_active_to_pass:          0
% 1.32/0.99  
% 1.32/0.99  ------ Superposition
% 1.32/0.99  
% 1.32/0.99  sup_time_total:                         0.
% 1.32/0.99  sup_time_generating:                    0.
% 1.32/0.99  sup_time_sim_full:                      0.
% 1.32/0.99  sup_time_sim_immed:                     0.
% 1.32/0.99  
% 1.32/0.99  sup_num_of_clauses:                     17
% 1.32/0.99  sup_num_in_active:                      12
% 1.32/0.99  sup_num_in_passive:                     5
% 1.32/0.99  sup_num_of_loops:                       12
% 1.32/0.99  sup_fw_superposition:                   2
% 1.32/0.99  sup_bw_superposition:                   1
% 1.32/0.99  sup_immediate_simplified:               0
% 1.32/0.99  sup_given_eliminated:                   0
% 1.32/0.99  comparisons_done:                       0
% 1.32/0.99  comparisons_avoided:                    0
% 1.32/0.99  
% 1.32/0.99  ------ Simplifications
% 1.32/0.99  
% 1.32/0.99  
% 1.32/0.99  sim_fw_subset_subsumed:                 0
% 1.32/0.99  sim_bw_subset_subsumed:                 0
% 1.32/0.99  sim_fw_subsumed:                        0
% 1.32/0.99  sim_bw_subsumed:                        0
% 1.32/0.99  sim_fw_subsumption_res:                 0
% 1.32/0.99  sim_bw_subsumption_res:                 0
% 1.32/0.99  sim_tautology_del:                      0
% 1.32/0.99  sim_eq_tautology_del:                   0
% 1.32/0.99  sim_eq_res_simp:                        0
% 1.32/0.99  sim_fw_demodulated:                     0
% 1.32/0.99  sim_bw_demodulated:                     0
% 1.32/0.99  sim_light_normalised:                   0
% 1.32/0.99  sim_joinable_taut:                      0
% 1.32/0.99  sim_joinable_simp:                      0
% 1.32/0.99  sim_ac_normalised:                      0
% 1.32/0.99  sim_smt_subsumption:                    0
% 1.32/0.99  
%------------------------------------------------------------------------------
