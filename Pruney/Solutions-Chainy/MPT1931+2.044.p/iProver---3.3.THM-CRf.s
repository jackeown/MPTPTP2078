%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:15 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 199 expanded)
%              Number of clauses        :   46 (  59 expanded)
%              Number of leaves         :   17 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  368 ( 854 expanded)
%              Number of equality atoms :   47 (  49 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f47])).

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

fof(f36,plain,(
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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_waybel_0(X0,sK5,u1_struct_0(X0))
        & l1_waybel_0(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK4,X1,u1_struct_0(sK4))
          & l1_waybel_0(X1,sK4)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r1_waybel_0(sK4,sK5,u1_struct_0(sK4))
    & l1_waybel_0(sK5,sK4)
    & ~ v2_struct_0(sK5)
    & l1_struct_0(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f38,f37])).

fof(f62,plain,(
    ~ r1_waybel_0(sK4,sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    l1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f34,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
        & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
                      & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f34,f33])).

fof(f53,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f4,f29])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1217,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1212,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1211,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1726,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1211])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_298,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_299,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X1,X0) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_1404,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_1406,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1404])).

cnf(c_1405,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1410,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1405])).

cnf(c_1742,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1726,c_1406,c_1410])).

cnf(c_1749,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_1742])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k6_subset_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1214,plain,
    ( k6_subset_1(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1895,plain,
    ( k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_1749,c_1214])).

cnf(c_15,plain,
    ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_17,negated_conjecture,
    ( ~ r1_waybel_0(sK4,sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_441,plain,
    ( r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k6_subset_1(u1_struct_0(X0),X2) != u1_struct_0(sK4)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_442,plain,
    ( r2_waybel_0(sK4,sK5,X0)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | k6_subset_1(u1_struct_0(sK4),X0) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,negated_conjecture,
    ( l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_18,negated_conjecture,
    ( l1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_446,plain,
    ( r2_waybel_0(sK4,sK5,X0)
    | k6_subset_1(u1_struct_0(sK4),X0) != u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_442,c_21,c_20,c_19,c_18])).

cnf(c_1201,plain,
    ( k6_subset_1(u1_struct_0(sK4),X0) != u1_struct_0(sK4)
    | r2_waybel_0(sK4,sK5,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_1955,plain,
    ( r2_waybel_0(sK4,sK5,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_1201])).

cnf(c_1783,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k1_xboole_0,sK1(u1_struct_0(sK5)))),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1404])).

cnf(c_1786,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k1_xboole_0,sK1(u1_struct_0(sK5)))),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1783])).

cnf(c_12,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1388,plain,
    ( ~ r2_waybel_0(sK4,sK5,X0)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,X0,X1)),X0)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1539,plain,
    ( ~ r2_waybel_0(sK4,sK5,X0)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5))
    | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,X0,sK1(u1_struct_0(sK5)))),X0)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1388])).

cnf(c_1782,plain,
    ( ~ r2_waybel_0(sK4,sK5,k1_xboole_0)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5))
    | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k1_xboole_0,sK1(u1_struct_0(sK5)))),k1_xboole_0)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1539])).

cnf(c_1784,plain,
    ( r2_waybel_0(sK4,sK5,k1_xboole_0) != iProver_top
    | l1_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k1_xboole_0,sK1(u1_struct_0(sK5)))),k1_xboole_0) = iProver_top
    | l1_struct_0(sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1782])).

cnf(c_6,plain,
    ( m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1460,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1465,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(c_25,plain,
    ( l1_waybel_0(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_24,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_23,plain,
    ( l1_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1955,c_1786,c_1784,c_1465,c_1410,c_25,c_24,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:15:20 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.33  % Running in FOF mode
% 2.28/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/0.94  
% 2.28/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.28/0.94  
% 2.28/0.94  ------  iProver source info
% 2.28/0.94  
% 2.28/0.94  git: date: 2020-06-30 10:37:57 +0100
% 2.28/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.28/0.94  git: non_committed_changes: false
% 2.28/0.94  git: last_make_outside_of_git: false
% 2.28/0.94  
% 2.28/0.94  ------ 
% 2.28/0.94  
% 2.28/0.94  ------ Input Options
% 2.28/0.94  
% 2.28/0.94  --out_options                           all
% 2.28/0.94  --tptp_safe_out                         true
% 2.28/0.94  --problem_path                          ""
% 2.28/0.94  --include_path                          ""
% 2.28/0.94  --clausifier                            res/vclausify_rel
% 2.28/0.94  --clausifier_options                    --mode clausify
% 2.28/0.94  --stdin                                 false
% 2.28/0.94  --stats_out                             all
% 2.28/0.94  
% 2.28/0.94  ------ General Options
% 2.28/0.94  
% 2.28/0.94  --fof                                   false
% 2.28/0.94  --time_out_real                         305.
% 2.28/0.94  --time_out_virtual                      -1.
% 2.28/0.94  --symbol_type_check                     false
% 2.28/0.94  --clausify_out                          false
% 2.28/0.94  --sig_cnt_out                           false
% 2.28/0.94  --trig_cnt_out                          false
% 2.28/0.94  --trig_cnt_out_tolerance                1.
% 2.28/0.94  --trig_cnt_out_sk_spl                   false
% 2.28/0.94  --abstr_cl_out                          false
% 2.28/0.94  
% 2.28/0.94  ------ Global Options
% 2.28/0.94  
% 2.28/0.94  --schedule                              default
% 2.28/0.94  --add_important_lit                     false
% 2.28/0.94  --prop_solver_per_cl                    1000
% 2.28/0.94  --min_unsat_core                        false
% 2.28/0.94  --soft_assumptions                      false
% 2.28/0.94  --soft_lemma_size                       3
% 2.28/0.94  --prop_impl_unit_size                   0
% 2.28/0.94  --prop_impl_unit                        []
% 2.28/0.94  --share_sel_clauses                     true
% 2.28/0.94  --reset_solvers                         false
% 2.28/0.94  --bc_imp_inh                            [conj_cone]
% 2.28/0.94  --conj_cone_tolerance                   3.
% 2.28/0.94  --extra_neg_conj                        none
% 2.28/0.94  --large_theory_mode                     true
% 2.28/0.94  --prolific_symb_bound                   200
% 2.28/0.94  --lt_threshold                          2000
% 2.28/0.94  --clause_weak_htbl                      true
% 2.28/0.94  --gc_record_bc_elim                     false
% 2.28/0.94  
% 2.28/0.94  ------ Preprocessing Options
% 2.28/0.94  
% 2.28/0.94  --preprocessing_flag                    true
% 2.28/0.94  --time_out_prep_mult                    0.1
% 2.28/0.94  --splitting_mode                        input
% 2.28/0.94  --splitting_grd                         true
% 2.28/0.94  --splitting_cvd                         false
% 2.28/0.94  --splitting_cvd_svl                     false
% 2.28/0.94  --splitting_nvd                         32
% 2.28/0.94  --sub_typing                            true
% 2.28/0.94  --prep_gs_sim                           true
% 2.28/0.94  --prep_unflatten                        true
% 2.28/0.94  --prep_res_sim                          true
% 2.28/0.94  --prep_upred                            true
% 2.28/0.94  --prep_sem_filter                       exhaustive
% 2.28/0.94  --prep_sem_filter_out                   false
% 2.28/0.94  --pred_elim                             true
% 2.28/0.94  --res_sim_input                         true
% 2.28/0.94  --eq_ax_congr_red                       true
% 2.28/0.94  --pure_diseq_elim                       true
% 2.28/0.94  --brand_transform                       false
% 2.28/0.94  --non_eq_to_eq                          false
% 2.28/0.94  --prep_def_merge                        true
% 2.28/0.94  --prep_def_merge_prop_impl              false
% 2.28/0.94  --prep_def_merge_mbd                    true
% 2.28/0.94  --prep_def_merge_tr_red                 false
% 2.28/0.94  --prep_def_merge_tr_cl                  false
% 2.28/0.94  --smt_preprocessing                     true
% 2.28/0.94  --smt_ac_axioms                         fast
% 2.28/0.94  --preprocessed_out                      false
% 2.28/0.94  --preprocessed_stats                    false
% 2.28/0.94  
% 2.28/0.94  ------ Abstraction refinement Options
% 2.28/0.94  
% 2.28/0.94  --abstr_ref                             []
% 2.28/0.94  --abstr_ref_prep                        false
% 2.28/0.94  --abstr_ref_until_sat                   false
% 2.28/0.94  --abstr_ref_sig_restrict                funpre
% 2.28/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.28/0.94  --abstr_ref_under                       []
% 2.28/0.94  
% 2.28/0.94  ------ SAT Options
% 2.28/0.94  
% 2.28/0.94  --sat_mode                              false
% 2.28/0.94  --sat_fm_restart_options                ""
% 2.28/0.94  --sat_gr_def                            false
% 2.28/0.94  --sat_epr_types                         true
% 2.28/0.94  --sat_non_cyclic_types                  false
% 2.28/0.94  --sat_finite_models                     false
% 2.28/0.94  --sat_fm_lemmas                         false
% 2.28/0.94  --sat_fm_prep                           false
% 2.28/0.94  --sat_fm_uc_incr                        true
% 2.28/0.94  --sat_out_model                         small
% 2.28/0.94  --sat_out_clauses                       false
% 2.28/0.94  
% 2.28/0.94  ------ QBF Options
% 2.28/0.94  
% 2.28/0.94  --qbf_mode                              false
% 2.28/0.94  --qbf_elim_univ                         false
% 2.28/0.94  --qbf_dom_inst                          none
% 2.28/0.94  --qbf_dom_pre_inst                      false
% 2.28/0.94  --qbf_sk_in                             false
% 2.28/0.94  --qbf_pred_elim                         true
% 2.28/0.94  --qbf_split                             512
% 2.28/0.94  
% 2.28/0.94  ------ BMC1 Options
% 2.28/0.94  
% 2.28/0.94  --bmc1_incremental                      false
% 2.28/0.94  --bmc1_axioms                           reachable_all
% 2.28/0.94  --bmc1_min_bound                        0
% 2.28/0.94  --bmc1_max_bound                        -1
% 2.28/0.94  --bmc1_max_bound_default                -1
% 2.28/0.94  --bmc1_symbol_reachability              true
% 2.28/0.94  --bmc1_property_lemmas                  false
% 2.28/0.94  --bmc1_k_induction                      false
% 2.28/0.94  --bmc1_non_equiv_states                 false
% 2.28/0.94  --bmc1_deadlock                         false
% 2.28/0.94  --bmc1_ucm                              false
% 2.28/0.94  --bmc1_add_unsat_core                   none
% 2.28/0.94  --bmc1_unsat_core_children              false
% 2.28/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.28/0.94  --bmc1_out_stat                         full
% 2.28/0.94  --bmc1_ground_init                      false
% 2.28/0.94  --bmc1_pre_inst_next_state              false
% 2.28/0.94  --bmc1_pre_inst_state                   false
% 2.28/0.94  --bmc1_pre_inst_reach_state             false
% 2.28/0.94  --bmc1_out_unsat_core                   false
% 2.28/0.94  --bmc1_aig_witness_out                  false
% 2.28/0.94  --bmc1_verbose                          false
% 2.28/0.94  --bmc1_dump_clauses_tptp                false
% 2.28/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.28/0.94  --bmc1_dump_file                        -
% 2.28/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.28/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.28/0.94  --bmc1_ucm_extend_mode                  1
% 2.28/0.94  --bmc1_ucm_init_mode                    2
% 2.28/0.94  --bmc1_ucm_cone_mode                    none
% 2.28/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.28/0.94  --bmc1_ucm_relax_model                  4
% 2.28/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.28/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.28/0.94  --bmc1_ucm_layered_model                none
% 2.28/0.94  --bmc1_ucm_max_lemma_size               10
% 2.28/0.94  
% 2.28/0.94  ------ AIG Options
% 2.28/0.94  
% 2.28/0.94  --aig_mode                              false
% 2.28/0.94  
% 2.28/0.94  ------ Instantiation Options
% 2.28/0.94  
% 2.28/0.94  --instantiation_flag                    true
% 2.28/0.94  --inst_sos_flag                         false
% 2.28/0.94  --inst_sos_phase                        true
% 2.28/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.28/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.28/0.94  --inst_lit_sel_side                     num_symb
% 2.28/0.94  --inst_solver_per_active                1400
% 2.28/0.94  --inst_solver_calls_frac                1.
% 2.28/0.94  --inst_passive_queue_type               priority_queues
% 2.28/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.28/0.94  --inst_passive_queues_freq              [25;2]
% 2.28/0.94  --inst_dismatching                      true
% 2.28/0.94  --inst_eager_unprocessed_to_passive     true
% 2.28/0.94  --inst_prop_sim_given                   true
% 2.28/0.94  --inst_prop_sim_new                     false
% 2.28/0.94  --inst_subs_new                         false
% 2.28/0.94  --inst_eq_res_simp                      false
% 2.28/0.94  --inst_subs_given                       false
% 2.28/0.94  --inst_orphan_elimination               true
% 2.28/0.94  --inst_learning_loop_flag               true
% 2.28/0.94  --inst_learning_start                   3000
% 2.28/0.94  --inst_learning_factor                  2
% 2.28/0.94  --inst_start_prop_sim_after_learn       3
% 2.28/0.94  --inst_sel_renew                        solver
% 2.28/0.94  --inst_lit_activity_flag                true
% 2.28/0.94  --inst_restr_to_given                   false
% 2.28/0.94  --inst_activity_threshold               500
% 2.28/0.94  --inst_out_proof                        true
% 2.28/0.94  
% 2.28/0.94  ------ Resolution Options
% 2.28/0.94  
% 2.28/0.94  --resolution_flag                       true
% 2.28/0.94  --res_lit_sel                           adaptive
% 2.28/0.94  --res_lit_sel_side                      none
% 2.28/0.94  --res_ordering                          kbo
% 2.28/0.94  --res_to_prop_solver                    active
% 2.28/0.94  --res_prop_simpl_new                    false
% 2.28/0.94  --res_prop_simpl_given                  true
% 2.28/0.94  --res_passive_queue_type                priority_queues
% 2.28/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.28/0.94  --res_passive_queues_freq               [15;5]
% 2.28/0.94  --res_forward_subs                      full
% 2.28/0.94  --res_backward_subs                     full
% 2.28/0.94  --res_forward_subs_resolution           true
% 2.28/0.94  --res_backward_subs_resolution          true
% 2.28/0.94  --res_orphan_elimination                true
% 2.28/0.94  --res_time_limit                        2.
% 2.28/0.94  --res_out_proof                         true
% 2.28/0.94  
% 2.28/0.94  ------ Superposition Options
% 2.28/0.94  
% 2.28/0.94  --superposition_flag                    true
% 2.28/0.94  --sup_passive_queue_type                priority_queues
% 2.28/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.28/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.28/0.94  --demod_completeness_check              fast
% 2.28/0.94  --demod_use_ground                      true
% 2.28/0.94  --sup_to_prop_solver                    passive
% 2.28/0.94  --sup_prop_simpl_new                    true
% 2.28/0.94  --sup_prop_simpl_given                  true
% 2.28/0.94  --sup_fun_splitting                     false
% 2.28/0.94  --sup_smt_interval                      50000
% 2.28/0.94  
% 2.28/0.94  ------ Superposition Simplification Setup
% 2.28/0.94  
% 2.28/0.94  --sup_indices_passive                   []
% 2.28/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.28/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.94  --sup_full_bw                           [BwDemod]
% 2.28/0.94  --sup_immed_triv                        [TrivRules]
% 2.28/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.28/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.94  --sup_immed_bw_main                     []
% 2.28/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.28/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.94  
% 2.28/0.94  ------ Combination Options
% 2.28/0.94  
% 2.28/0.94  --comb_res_mult                         3
% 2.28/0.94  --comb_sup_mult                         2
% 2.28/0.94  --comb_inst_mult                        10
% 2.28/0.94  
% 2.28/0.94  ------ Debug Options
% 2.28/0.94  
% 2.28/0.94  --dbg_backtrace                         false
% 2.28/0.94  --dbg_dump_prop_clauses                 false
% 2.28/0.94  --dbg_dump_prop_clauses_file            -
% 2.28/0.94  --dbg_out_stat                          false
% 2.28/0.94  ------ Parsing...
% 2.28/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.28/0.94  
% 2.28/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.28/0.94  
% 2.28/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.28/0.94  
% 2.28/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.28/0.94  ------ Proving...
% 2.28/0.94  ------ Problem Properties 
% 2.28/0.94  
% 2.28/0.94  
% 2.28/0.94  clauses                                 18
% 2.28/0.94  conjectures                             4
% 2.28/0.94  EPR                                     5
% 2.28/0.94  Horn                                    12
% 2.28/0.94  unary                                   6
% 2.28/0.94  binary                                  6
% 2.28/0.94  lits                                    54
% 2.28/0.94  lits eq                                 3
% 2.28/0.94  fd_pure                                 0
% 2.28/0.94  fd_pseudo                               0
% 2.28/0.94  fd_cond                                 0
% 2.28/0.94  fd_pseudo_cond                          0
% 2.28/0.94  AC symbols                              0
% 2.28/0.94  
% 2.28/0.94  ------ Schedule dynamic 5 is on 
% 2.28/0.94  
% 2.28/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.28/0.94  
% 2.28/0.94  
% 2.28/0.94  ------ 
% 2.28/0.94  Current options:
% 2.28/0.94  ------ 
% 2.28/0.94  
% 2.28/0.94  ------ Input Options
% 2.28/0.94  
% 2.28/0.94  --out_options                           all
% 2.28/0.94  --tptp_safe_out                         true
% 2.28/0.94  --problem_path                          ""
% 2.28/0.94  --include_path                          ""
% 2.28/0.94  --clausifier                            res/vclausify_rel
% 2.28/0.94  --clausifier_options                    --mode clausify
% 2.28/0.94  --stdin                                 false
% 2.28/0.94  --stats_out                             all
% 2.28/0.94  
% 2.28/0.94  ------ General Options
% 2.28/0.94  
% 2.28/0.94  --fof                                   false
% 2.28/0.94  --time_out_real                         305.
% 2.28/0.94  --time_out_virtual                      -1.
% 2.28/0.94  --symbol_type_check                     false
% 2.28/0.94  --clausify_out                          false
% 2.28/0.94  --sig_cnt_out                           false
% 2.28/0.94  --trig_cnt_out                          false
% 2.28/0.94  --trig_cnt_out_tolerance                1.
% 2.28/0.94  --trig_cnt_out_sk_spl                   false
% 2.28/0.94  --abstr_cl_out                          false
% 2.28/0.94  
% 2.28/0.94  ------ Global Options
% 2.28/0.94  
% 2.28/0.94  --schedule                              default
% 2.28/0.94  --add_important_lit                     false
% 2.28/0.94  --prop_solver_per_cl                    1000
% 2.28/0.94  --min_unsat_core                        false
% 2.28/0.94  --soft_assumptions                      false
% 2.28/0.94  --soft_lemma_size                       3
% 2.28/0.94  --prop_impl_unit_size                   0
% 2.28/0.94  --prop_impl_unit                        []
% 2.28/0.94  --share_sel_clauses                     true
% 2.28/0.94  --reset_solvers                         false
% 2.28/0.94  --bc_imp_inh                            [conj_cone]
% 2.28/0.94  --conj_cone_tolerance                   3.
% 2.28/0.94  --extra_neg_conj                        none
% 2.28/0.94  --large_theory_mode                     true
% 2.28/0.94  --prolific_symb_bound                   200
% 2.28/0.94  --lt_threshold                          2000
% 2.28/0.94  --clause_weak_htbl                      true
% 2.28/0.94  --gc_record_bc_elim                     false
% 2.28/0.94  
% 2.28/0.94  ------ Preprocessing Options
% 2.28/0.94  
% 2.28/0.94  --preprocessing_flag                    true
% 2.28/0.94  --time_out_prep_mult                    0.1
% 2.28/0.94  --splitting_mode                        input
% 2.28/0.94  --splitting_grd                         true
% 2.28/0.94  --splitting_cvd                         false
% 2.28/0.94  --splitting_cvd_svl                     false
% 2.28/0.94  --splitting_nvd                         32
% 2.28/0.94  --sub_typing                            true
% 2.28/0.94  --prep_gs_sim                           true
% 2.28/0.94  --prep_unflatten                        true
% 2.28/0.94  --prep_res_sim                          true
% 2.28/0.94  --prep_upred                            true
% 2.28/0.94  --prep_sem_filter                       exhaustive
% 2.28/0.94  --prep_sem_filter_out                   false
% 2.28/0.94  --pred_elim                             true
% 2.28/0.94  --res_sim_input                         true
% 2.28/0.94  --eq_ax_congr_red                       true
% 2.28/0.94  --pure_diseq_elim                       true
% 2.28/0.94  --brand_transform                       false
% 2.28/0.94  --non_eq_to_eq                          false
% 2.28/0.94  --prep_def_merge                        true
% 2.28/0.94  --prep_def_merge_prop_impl              false
% 2.28/0.94  --prep_def_merge_mbd                    true
% 2.28/0.94  --prep_def_merge_tr_red                 false
% 2.28/0.94  --prep_def_merge_tr_cl                  false
% 2.28/0.94  --smt_preprocessing                     true
% 2.28/0.94  --smt_ac_axioms                         fast
% 2.28/0.94  --preprocessed_out                      false
% 2.28/0.94  --preprocessed_stats                    false
% 2.28/0.94  
% 2.28/0.94  ------ Abstraction refinement Options
% 2.28/0.94  
% 2.28/0.94  --abstr_ref                             []
% 2.28/0.94  --abstr_ref_prep                        false
% 2.28/0.94  --abstr_ref_until_sat                   false
% 2.28/0.94  --abstr_ref_sig_restrict                funpre
% 2.28/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.28/0.94  --abstr_ref_under                       []
% 2.28/0.94  
% 2.28/0.94  ------ SAT Options
% 2.28/0.94  
% 2.28/0.94  --sat_mode                              false
% 2.28/0.94  --sat_fm_restart_options                ""
% 2.28/0.94  --sat_gr_def                            false
% 2.28/0.94  --sat_epr_types                         true
% 2.28/0.94  --sat_non_cyclic_types                  false
% 2.28/0.94  --sat_finite_models                     false
% 2.28/0.94  --sat_fm_lemmas                         false
% 2.28/0.94  --sat_fm_prep                           false
% 2.28/0.94  --sat_fm_uc_incr                        true
% 2.28/0.94  --sat_out_model                         small
% 2.28/0.94  --sat_out_clauses                       false
% 2.28/0.94  
% 2.28/0.94  ------ QBF Options
% 2.28/0.94  
% 2.28/0.94  --qbf_mode                              false
% 2.28/0.94  --qbf_elim_univ                         false
% 2.28/0.94  --qbf_dom_inst                          none
% 2.28/0.94  --qbf_dom_pre_inst                      false
% 2.28/0.94  --qbf_sk_in                             false
% 2.28/0.94  --qbf_pred_elim                         true
% 2.28/0.94  --qbf_split                             512
% 2.28/0.94  
% 2.28/0.94  ------ BMC1 Options
% 2.28/0.94  
% 2.28/0.94  --bmc1_incremental                      false
% 2.28/0.94  --bmc1_axioms                           reachable_all
% 2.28/0.94  --bmc1_min_bound                        0
% 2.28/0.94  --bmc1_max_bound                        -1
% 2.28/0.94  --bmc1_max_bound_default                -1
% 2.28/0.94  --bmc1_symbol_reachability              true
% 2.28/0.94  --bmc1_property_lemmas                  false
% 2.28/0.94  --bmc1_k_induction                      false
% 2.28/0.94  --bmc1_non_equiv_states                 false
% 2.28/0.94  --bmc1_deadlock                         false
% 2.28/0.94  --bmc1_ucm                              false
% 2.28/0.94  --bmc1_add_unsat_core                   none
% 2.28/0.94  --bmc1_unsat_core_children              false
% 2.28/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.28/0.94  --bmc1_out_stat                         full
% 2.28/0.94  --bmc1_ground_init                      false
% 2.28/0.94  --bmc1_pre_inst_next_state              false
% 2.28/0.94  --bmc1_pre_inst_state                   false
% 2.28/0.94  --bmc1_pre_inst_reach_state             false
% 2.28/0.94  --bmc1_out_unsat_core                   false
% 2.28/0.94  --bmc1_aig_witness_out                  false
% 2.28/0.94  --bmc1_verbose                          false
% 2.28/0.94  --bmc1_dump_clauses_tptp                false
% 2.28/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.28/0.94  --bmc1_dump_file                        -
% 2.28/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.28/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.28/0.94  --bmc1_ucm_extend_mode                  1
% 2.28/0.94  --bmc1_ucm_init_mode                    2
% 2.28/0.94  --bmc1_ucm_cone_mode                    none
% 2.28/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.28/0.94  --bmc1_ucm_relax_model                  4
% 2.28/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.28/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.28/0.94  --bmc1_ucm_layered_model                none
% 2.28/0.94  --bmc1_ucm_max_lemma_size               10
% 2.28/0.94  
% 2.28/0.94  ------ AIG Options
% 2.28/0.94  
% 2.28/0.94  --aig_mode                              false
% 2.28/0.94  
% 2.28/0.94  ------ Instantiation Options
% 2.28/0.94  
% 2.28/0.94  --instantiation_flag                    true
% 2.28/0.94  --inst_sos_flag                         false
% 2.28/0.94  --inst_sos_phase                        true
% 2.28/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.28/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.28/0.94  --inst_lit_sel_side                     none
% 2.28/0.94  --inst_solver_per_active                1400
% 2.28/0.94  --inst_solver_calls_frac                1.
% 2.28/0.94  --inst_passive_queue_type               priority_queues
% 2.28/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.28/0.94  --inst_passive_queues_freq              [25;2]
% 2.28/0.94  --inst_dismatching                      true
% 2.28/0.94  --inst_eager_unprocessed_to_passive     true
% 2.28/0.94  --inst_prop_sim_given                   true
% 2.28/0.94  --inst_prop_sim_new                     false
% 2.28/0.94  --inst_subs_new                         false
% 2.28/0.94  --inst_eq_res_simp                      false
% 2.28/0.94  --inst_subs_given                       false
% 2.28/0.94  --inst_orphan_elimination               true
% 2.28/0.94  --inst_learning_loop_flag               true
% 2.28/0.94  --inst_learning_start                   3000
% 2.28/0.94  --inst_learning_factor                  2
% 2.28/0.94  --inst_start_prop_sim_after_learn       3
% 2.28/0.94  --inst_sel_renew                        solver
% 2.28/0.94  --inst_lit_activity_flag                true
% 2.28/0.94  --inst_restr_to_given                   false
% 2.28/0.94  --inst_activity_threshold               500
% 2.28/0.94  --inst_out_proof                        true
% 2.28/0.94  
% 2.28/0.94  ------ Resolution Options
% 2.28/0.94  
% 2.28/0.94  --resolution_flag                       false
% 2.28/0.94  --res_lit_sel                           adaptive
% 2.28/0.94  --res_lit_sel_side                      none
% 2.28/0.94  --res_ordering                          kbo
% 2.28/0.94  --res_to_prop_solver                    active
% 2.28/0.94  --res_prop_simpl_new                    false
% 2.28/0.94  --res_prop_simpl_given                  true
% 2.28/0.94  --res_passive_queue_type                priority_queues
% 2.28/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.28/0.94  --res_passive_queues_freq               [15;5]
% 2.28/0.94  --res_forward_subs                      full
% 2.28/0.94  --res_backward_subs                     full
% 2.28/0.94  --res_forward_subs_resolution           true
% 2.28/0.94  --res_backward_subs_resolution          true
% 2.28/0.94  --res_orphan_elimination                true
% 2.28/0.94  --res_time_limit                        2.
% 2.28/0.94  --res_out_proof                         true
% 2.28/0.94  
% 2.28/0.94  ------ Superposition Options
% 2.28/0.94  
% 2.28/0.94  --superposition_flag                    true
% 2.28/0.94  --sup_passive_queue_type                priority_queues
% 2.28/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.28/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.28/0.94  --demod_completeness_check              fast
% 2.28/0.94  --demod_use_ground                      true
% 2.28/0.94  --sup_to_prop_solver                    passive
% 2.28/0.94  --sup_prop_simpl_new                    true
% 2.28/0.94  --sup_prop_simpl_given                  true
% 2.28/0.94  --sup_fun_splitting                     false
% 2.28/0.94  --sup_smt_interval                      50000
% 2.28/0.94  
% 2.28/0.94  ------ Superposition Simplification Setup
% 2.28/0.94  
% 2.28/0.94  --sup_indices_passive                   []
% 2.28/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.28/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.94  --sup_full_bw                           [BwDemod]
% 2.28/0.94  --sup_immed_triv                        [TrivRules]
% 2.28/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.28/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.94  --sup_immed_bw_main                     []
% 2.28/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.28/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.94  
% 2.28/0.94  ------ Combination Options
% 2.28/0.94  
% 2.28/0.94  --comb_res_mult                         3
% 2.28/0.94  --comb_sup_mult                         2
% 2.28/0.94  --comb_inst_mult                        10
% 2.28/0.94  
% 2.28/0.94  ------ Debug Options
% 2.28/0.94  
% 2.28/0.94  --dbg_backtrace                         false
% 2.28/0.94  --dbg_dump_prop_clauses                 false
% 2.28/0.94  --dbg_dump_prop_clauses_file            -
% 2.28/0.94  --dbg_out_stat                          false
% 2.28/0.94  
% 2.28/0.94  
% 2.28/0.94  
% 2.28/0.94  
% 2.28/0.94  ------ Proving...
% 2.28/0.94  
% 2.28/0.94  
% 2.28/0.94  % SZS status Theorem for theBenchmark.p
% 2.28/0.94  
% 2.28/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 2.28/0.94  
% 2.28/0.94  fof(f2,axiom,(
% 2.28/0.94    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.28/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.94  
% 2.28/0.94  fof(f13,plain,(
% 2.28/0.94    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.28/0.94    inference(rectify,[],[f2])).
% 2.28/0.94  
% 2.28/0.94  fof(f16,plain,(
% 2.28/0.94    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.28/0.94    inference(ennf_transformation,[],[f13])).
% 2.28/0.94  
% 2.28/0.94  fof(f26,plain,(
% 2.28/0.94    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.28/0.94    introduced(choice_axiom,[])).
% 2.28/0.94  
% 2.28/0.94  fof(f27,plain,(
% 2.28/0.94    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.28/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f26])).
% 2.28/0.94  
% 2.28/0.94  fof(f42,plain,(
% 2.28/0.94    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.28/0.94    inference(cnf_transformation,[],[f27])).
% 2.28/0.94  
% 2.28/0.94  fof(f6,axiom,(
% 2.28/0.94    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.28/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.94  
% 2.28/0.94  fof(f48,plain,(
% 2.28/0.94    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.28/0.94    inference(cnf_transformation,[],[f6])).
% 2.28/0.94  
% 2.28/0.94  fof(f7,axiom,(
% 2.28/0.94    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.28/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.94  
% 2.28/0.94  fof(f17,plain,(
% 2.28/0.94    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.28/0.94    inference(ennf_transformation,[],[f7])).
% 2.28/0.94  
% 2.28/0.94  fof(f18,plain,(
% 2.28/0.94    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.28/0.94    inference(flattening,[],[f17])).
% 2.28/0.94  
% 2.28/0.94  fof(f49,plain,(
% 2.28/0.94    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.28/0.94    inference(cnf_transformation,[],[f18])).
% 2.28/0.94  
% 2.28/0.94  fof(f1,axiom,(
% 2.28/0.94    v1_xboole_0(k1_xboole_0)),
% 2.28/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.94  
% 2.28/0.94  fof(f40,plain,(
% 2.28/0.94    v1_xboole_0(k1_xboole_0)),
% 2.28/0.94    inference(cnf_transformation,[],[f1])).
% 2.28/0.94  
% 2.28/0.94  fof(f8,axiom,(
% 2.28/0.94    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.28/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.94  
% 2.28/0.94  fof(f19,plain,(
% 2.28/0.94    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.28/0.94    inference(ennf_transformation,[],[f8])).
% 2.28/0.94  
% 2.28/0.94  fof(f50,plain,(
% 2.28/0.94    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.28/0.94    inference(cnf_transformation,[],[f19])).
% 2.28/0.94  
% 2.28/0.94  fof(f3,axiom,(
% 2.28/0.94    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.28/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.94  
% 2.28/0.94  fof(f28,plain,(
% 2.28/0.94    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.28/0.94    inference(nnf_transformation,[],[f3])).
% 2.28/0.94  
% 2.28/0.94  fof(f44,plain,(
% 2.28/0.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.28/0.94    inference(cnf_transformation,[],[f28])).
% 2.28/0.94  
% 2.28/0.94  fof(f5,axiom,(
% 2.28/0.94    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.28/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.94  
% 2.28/0.94  fof(f47,plain,(
% 2.28/0.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.28/0.94    inference(cnf_transformation,[],[f5])).
% 2.28/0.94  
% 2.28/0.94  fof(f64,plain,(
% 2.28/0.94    ( ! [X0,X1] : (k6_subset_1(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.28/0.94    inference(definition_unfolding,[],[f44,f47])).
% 2.28/0.94  
% 2.28/0.94  fof(f10,axiom,(
% 2.28/0.94    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 2.28/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.94  
% 2.28/0.94  fof(f22,plain,(
% 2.28/0.94    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.28/0.94    inference(ennf_transformation,[],[f10])).
% 2.28/0.94  
% 2.28/0.94  fof(f23,plain,(
% 2.28/0.94    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.28/0.94    inference(flattening,[],[f22])).
% 2.28/0.94  
% 2.28/0.94  fof(f36,plain,(
% 2.28/0.94    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.28/0.94    inference(nnf_transformation,[],[f23])).
% 2.28/0.94  
% 2.28/0.94  fof(f57,plain,(
% 2.28/0.94    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.28/0.94    inference(cnf_transformation,[],[f36])).
% 2.28/0.94  
% 2.28/0.94  fof(f11,conjecture,(
% 2.28/0.94    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 2.28/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.94  
% 2.28/0.94  fof(f12,negated_conjecture,(
% 2.28/0.94    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 2.28/0.94    inference(negated_conjecture,[],[f11])).
% 2.28/0.94  
% 2.28/0.94  fof(f14,plain,(
% 2.28/0.94    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 2.28/0.94    inference(pure_predicate_removal,[],[f12])).
% 2.28/0.94  
% 2.28/0.94  fof(f15,plain,(
% 2.28/0.94    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 2.28/0.94    inference(pure_predicate_removal,[],[f14])).
% 2.28/0.94  
% 2.28/0.94  fof(f24,plain,(
% 2.28/0.94    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 2.28/0.94    inference(ennf_transformation,[],[f15])).
% 2.28/0.94  
% 2.28/0.94  fof(f25,plain,(
% 2.28/0.94    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 2.28/0.94    inference(flattening,[],[f24])).
% 2.28/0.94  
% 2.28/0.94  fof(f38,plain,(
% 2.28/0.94    ( ! [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (~r1_waybel_0(X0,sK5,u1_struct_0(X0)) & l1_waybel_0(sK5,X0) & ~v2_struct_0(sK5))) )),
% 2.28/0.94    introduced(choice_axiom,[])).
% 2.28/0.94  
% 2.28/0.94  fof(f37,plain,(
% 2.28/0.94    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK4,X1,u1_struct_0(sK4)) & l1_waybel_0(X1,sK4) & ~v2_struct_0(X1)) & l1_struct_0(sK4) & ~v2_struct_0(sK4))),
% 2.28/0.94    introduced(choice_axiom,[])).
% 2.28/0.94  
% 2.28/0.94  fof(f39,plain,(
% 2.28/0.94    (~r1_waybel_0(sK4,sK5,u1_struct_0(sK4)) & l1_waybel_0(sK5,sK4) & ~v2_struct_0(sK5)) & l1_struct_0(sK4) & ~v2_struct_0(sK4)),
% 2.28/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f38,f37])).
% 2.28/0.94  
% 2.28/0.94  fof(f62,plain,(
% 2.28/0.94    ~r1_waybel_0(sK4,sK5,u1_struct_0(sK4))),
% 2.28/0.94    inference(cnf_transformation,[],[f39])).
% 2.28/0.94  
% 2.28/0.94  fof(f58,plain,(
% 2.28/0.94    ~v2_struct_0(sK4)),
% 2.28/0.94    inference(cnf_transformation,[],[f39])).
% 2.28/0.94  
% 2.28/0.94  fof(f59,plain,(
% 2.28/0.94    l1_struct_0(sK4)),
% 2.28/0.94    inference(cnf_transformation,[],[f39])).
% 2.28/0.94  
% 2.28/0.94  fof(f60,plain,(
% 2.28/0.94    ~v2_struct_0(sK5)),
% 2.28/0.94    inference(cnf_transformation,[],[f39])).
% 2.28/0.94  
% 2.28/0.94  fof(f61,plain,(
% 2.28/0.94    l1_waybel_0(sK5,sK4)),
% 2.28/0.94    inference(cnf_transformation,[],[f39])).
% 2.28/0.94  
% 2.28/0.94  fof(f9,axiom,(
% 2.28/0.94    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 2.28/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.94  
% 2.28/0.94  fof(f20,plain,(
% 2.28/0.94    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.28/0.94    inference(ennf_transformation,[],[f9])).
% 2.28/0.94  
% 2.28/0.94  fof(f21,plain,(
% 2.28/0.94    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.28/0.94    inference(flattening,[],[f20])).
% 2.28/0.94  
% 2.28/0.94  fof(f31,plain,(
% 2.28/0.94    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.28/0.94    inference(nnf_transformation,[],[f21])).
% 2.28/0.94  
% 2.28/0.94  fof(f32,plain,(
% 2.28/0.94    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.28/0.94    inference(rectify,[],[f31])).
% 2.28/0.94  
% 2.28/0.94  fof(f34,plain,(
% 2.28/0.94    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))))),
% 2.28/0.94    introduced(choice_axiom,[])).
% 2.28/0.94  
% 2.28/0.94  fof(f33,plain,(
% 2.28/0.94    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 2.28/0.94    introduced(choice_axiom,[])).
% 2.28/0.94  
% 2.28/0.94  fof(f35,plain,(
% 2.28/0.94    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.28/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f34,f33])).
% 2.28/0.94  
% 2.28/0.94  fof(f53,plain,(
% 2.28/0.94    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.28/0.94    inference(cnf_transformation,[],[f35])).
% 2.28/0.94  
% 2.28/0.94  fof(f4,axiom,(
% 2.28/0.94    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.28/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.94  
% 2.28/0.94  fof(f29,plain,(
% 2.28/0.94    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK1(X0),X0))),
% 2.28/0.94    introduced(choice_axiom,[])).
% 2.28/0.94  
% 2.28/0.94  fof(f30,plain,(
% 2.28/0.94    ! [X0] : m1_subset_1(sK1(X0),X0)),
% 2.28/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f4,f29])).
% 2.28/0.94  
% 2.28/0.94  fof(f46,plain,(
% 2.28/0.94    ( ! [X0] : (m1_subset_1(sK1(X0),X0)) )),
% 2.28/0.94    inference(cnf_transformation,[],[f30])).
% 2.28/0.94  
% 2.28/0.94  cnf(c_2,plain,
% 2.28/0.94      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 2.28/0.94      inference(cnf_transformation,[],[f42]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1217,plain,
% 2.28/0.94      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 2.28/0.94      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.28/0.94      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_7,plain,
% 2.28/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.28/0.94      inference(cnf_transformation,[],[f48]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1212,plain,
% 2.28/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.28/0.94      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_8,plain,
% 2.28/0.94      ( m1_subset_1(X0,X1)
% 2.28/0.94      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.28/0.94      | ~ r2_hidden(X0,X2) ),
% 2.28/0.94      inference(cnf_transformation,[],[f49]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1211,plain,
% 2.28/0.94      ( m1_subset_1(X0,X1) = iProver_top
% 2.28/0.94      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.28/0.94      | r2_hidden(X0,X2) != iProver_top ),
% 2.28/0.94      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1726,plain,
% 2.28/0.94      ( m1_subset_1(X0,X1) = iProver_top
% 2.28/0.94      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.28/0.94      inference(superposition,[status(thm)],[c_1212,c_1211]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_0,plain,
% 2.28/0.94      ( v1_xboole_0(k1_xboole_0) ),
% 2.28/0.94      inference(cnf_transformation,[],[f40]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_9,plain,
% 2.28/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.28/0.94      | ~ r2_hidden(X2,X0)
% 2.28/0.94      | ~ v1_xboole_0(X1) ),
% 2.28/0.94      inference(cnf_transformation,[],[f50]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_298,plain,
% 2.28/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.28/0.94      | ~ r2_hidden(X2,X0)
% 2.28/0.94      | k1_xboole_0 != X1 ),
% 2.28/0.94      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_299,plain,
% 2.28/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~ r2_hidden(X1,X0) ),
% 2.28/0.94      inference(unflattening,[status(thm)],[c_298]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1404,plain,
% 2.28/0.94      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 2.28/0.94      | ~ r2_hidden(X0,k1_xboole_0) ),
% 2.28/0.94      inference(instantiation,[status(thm)],[c_299]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1406,plain,
% 2.28/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.28/0.94      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.28/0.94      inference(predicate_to_equality,[status(thm)],[c_1404]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1405,plain,
% 2.28/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 2.28/0.94      inference(instantiation,[status(thm)],[c_7]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1410,plain,
% 2.28/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.28/0.94      inference(predicate_to_equality,[status(thm)],[c_1405]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1742,plain,
% 2.28/0.94      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.28/0.94      inference(global_propositional_subsumption,
% 2.28/0.94                [status(thm)],
% 2.28/0.94                [c_1726,c_1406,c_1410]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1749,plain,
% 2.28/0.94      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 2.28/0.94      inference(superposition,[status(thm)],[c_1217,c_1742]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_5,plain,
% 2.28/0.94      ( ~ r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) = X0 ),
% 2.28/0.94      inference(cnf_transformation,[],[f64]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1214,plain,
% 2.28/0.94      ( k6_subset_1(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 2.28/0.94      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1895,plain,
% 2.28/0.94      ( k6_subset_1(X0,k1_xboole_0) = X0 ),
% 2.28/0.94      inference(superposition,[status(thm)],[c_1749,c_1214]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_15,plain,
% 2.28/0.94      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 2.28/0.94      | r2_waybel_0(X0,X1,X2)
% 2.28/0.94      | ~ l1_waybel_0(X1,X0)
% 2.28/0.94      | ~ l1_struct_0(X0)
% 2.28/0.94      | v2_struct_0(X0)
% 2.28/0.94      | v2_struct_0(X1) ),
% 2.28/0.94      inference(cnf_transformation,[],[f57]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_17,negated_conjecture,
% 2.28/0.94      ( ~ r1_waybel_0(sK4,sK5,u1_struct_0(sK4)) ),
% 2.28/0.94      inference(cnf_transformation,[],[f62]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_441,plain,
% 2.28/0.94      ( r2_waybel_0(X0,X1,X2)
% 2.28/0.94      | ~ l1_waybel_0(X1,X0)
% 2.28/0.94      | ~ l1_struct_0(X0)
% 2.28/0.94      | v2_struct_0(X0)
% 2.28/0.94      | v2_struct_0(X1)
% 2.28/0.94      | k6_subset_1(u1_struct_0(X0),X2) != u1_struct_0(sK4)
% 2.28/0.94      | sK5 != X1
% 2.28/0.94      | sK4 != X0 ),
% 2.28/0.94      inference(resolution_lifted,[status(thm)],[c_15,c_17]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_442,plain,
% 2.28/0.94      ( r2_waybel_0(sK4,sK5,X0)
% 2.28/0.94      | ~ l1_waybel_0(sK5,sK4)
% 2.28/0.94      | ~ l1_struct_0(sK4)
% 2.28/0.94      | v2_struct_0(sK5)
% 2.28/0.94      | v2_struct_0(sK4)
% 2.28/0.94      | k6_subset_1(u1_struct_0(sK4),X0) != u1_struct_0(sK4) ),
% 2.28/0.94      inference(unflattening,[status(thm)],[c_441]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_21,negated_conjecture,
% 2.28/0.94      ( ~ v2_struct_0(sK4) ),
% 2.28/0.94      inference(cnf_transformation,[],[f58]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_20,negated_conjecture,
% 2.28/0.94      ( l1_struct_0(sK4) ),
% 2.28/0.94      inference(cnf_transformation,[],[f59]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_19,negated_conjecture,
% 2.28/0.94      ( ~ v2_struct_0(sK5) ),
% 2.28/0.94      inference(cnf_transformation,[],[f60]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_18,negated_conjecture,
% 2.28/0.94      ( l1_waybel_0(sK5,sK4) ),
% 2.28/0.94      inference(cnf_transformation,[],[f61]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_446,plain,
% 2.28/0.94      ( r2_waybel_0(sK4,sK5,X0)
% 2.28/0.94      | k6_subset_1(u1_struct_0(sK4),X0) != u1_struct_0(sK4) ),
% 2.28/0.94      inference(global_propositional_subsumption,
% 2.28/0.94                [status(thm)],
% 2.28/0.94                [c_442,c_21,c_20,c_19,c_18]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1201,plain,
% 2.28/0.94      ( k6_subset_1(u1_struct_0(sK4),X0) != u1_struct_0(sK4)
% 2.28/0.94      | r2_waybel_0(sK4,sK5,X0) = iProver_top ),
% 2.28/0.94      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1955,plain,
% 2.28/0.94      ( r2_waybel_0(sK4,sK5,k1_xboole_0) = iProver_top ),
% 2.28/0.94      inference(superposition,[status(thm)],[c_1895,c_1201]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1783,plain,
% 2.28/0.94      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 2.28/0.94      | ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k1_xboole_0,sK1(u1_struct_0(sK5)))),k1_xboole_0) ),
% 2.28/0.94      inference(instantiation,[status(thm)],[c_1404]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1786,plain,
% 2.28/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.28/0.94      | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k1_xboole_0,sK1(u1_struct_0(sK5)))),k1_xboole_0) != iProver_top ),
% 2.28/0.94      inference(predicate_to_equality,[status(thm)],[c_1783]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_12,plain,
% 2.28/0.94      ( ~ r2_waybel_0(X0,X1,X2)
% 2.28/0.94      | ~ l1_waybel_0(X1,X0)
% 2.28/0.94      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.28/0.94      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
% 2.28/0.94      | ~ l1_struct_0(X0)
% 2.28/0.94      | v2_struct_0(X0)
% 2.28/0.94      | v2_struct_0(X1) ),
% 2.28/0.94      inference(cnf_transformation,[],[f53]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1388,plain,
% 2.28/0.94      ( ~ r2_waybel_0(sK4,sK5,X0)
% 2.28/0.94      | ~ l1_waybel_0(sK5,sK4)
% 2.28/0.94      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 2.28/0.94      | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,X0,X1)),X0)
% 2.28/0.94      | ~ l1_struct_0(sK4)
% 2.28/0.94      | v2_struct_0(sK5)
% 2.28/0.94      | v2_struct_0(sK4) ),
% 2.28/0.94      inference(instantiation,[status(thm)],[c_12]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1539,plain,
% 2.28/0.94      ( ~ r2_waybel_0(sK4,sK5,X0)
% 2.28/0.94      | ~ l1_waybel_0(sK5,sK4)
% 2.28/0.94      | ~ m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5))
% 2.28/0.94      | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,X0,sK1(u1_struct_0(sK5)))),X0)
% 2.28/0.94      | ~ l1_struct_0(sK4)
% 2.28/0.94      | v2_struct_0(sK5)
% 2.28/0.94      | v2_struct_0(sK4) ),
% 2.28/0.94      inference(instantiation,[status(thm)],[c_1388]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1782,plain,
% 2.28/0.94      ( ~ r2_waybel_0(sK4,sK5,k1_xboole_0)
% 2.28/0.94      | ~ l1_waybel_0(sK5,sK4)
% 2.28/0.94      | ~ m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5))
% 2.28/0.94      | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k1_xboole_0,sK1(u1_struct_0(sK5)))),k1_xboole_0)
% 2.28/0.94      | ~ l1_struct_0(sK4)
% 2.28/0.94      | v2_struct_0(sK5)
% 2.28/0.94      | v2_struct_0(sK4) ),
% 2.28/0.94      inference(instantiation,[status(thm)],[c_1539]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1784,plain,
% 2.28/0.94      ( r2_waybel_0(sK4,sK5,k1_xboole_0) != iProver_top
% 2.28/0.94      | l1_waybel_0(sK5,sK4) != iProver_top
% 2.28/0.94      | m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5)) != iProver_top
% 2.28/0.94      | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k1_xboole_0,sK1(u1_struct_0(sK5)))),k1_xboole_0) = iProver_top
% 2.28/0.94      | l1_struct_0(sK4) != iProver_top
% 2.28/0.94      | v2_struct_0(sK5) = iProver_top
% 2.28/0.94      | v2_struct_0(sK4) = iProver_top ),
% 2.28/0.94      inference(predicate_to_equality,[status(thm)],[c_1782]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_6,plain,
% 2.28/0.94      ( m1_subset_1(sK1(X0),X0) ),
% 2.28/0.94      inference(cnf_transformation,[],[f46]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1460,plain,
% 2.28/0.94      ( m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5)) ),
% 2.28/0.94      inference(instantiation,[status(thm)],[c_6]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_1465,plain,
% 2.28/0.94      ( m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5)) = iProver_top ),
% 2.28/0.94      inference(predicate_to_equality,[status(thm)],[c_1460]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_25,plain,
% 2.28/0.94      ( l1_waybel_0(sK5,sK4) = iProver_top ),
% 2.28/0.94      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_24,plain,
% 2.28/0.94      ( v2_struct_0(sK5) != iProver_top ),
% 2.28/0.94      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_23,plain,
% 2.28/0.94      ( l1_struct_0(sK4) = iProver_top ),
% 2.28/0.94      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(c_22,plain,
% 2.28/0.94      ( v2_struct_0(sK4) != iProver_top ),
% 2.28/0.94      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.28/0.94  
% 2.28/0.94  cnf(contradiction,plain,
% 2.28/0.94      ( $false ),
% 2.28/0.94      inference(minisat,
% 2.28/0.94                [status(thm)],
% 2.28/0.94                [c_1955,c_1786,c_1784,c_1465,c_1410,c_25,c_24,c_23,c_22]) ).
% 2.28/0.94  
% 2.28/0.94  
% 2.28/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 2.28/0.94  
% 2.28/0.94  ------                               Statistics
% 2.28/0.94  
% 2.28/0.94  ------ General
% 2.28/0.94  
% 2.28/0.94  abstr_ref_over_cycles:                  0
% 2.28/0.94  abstr_ref_under_cycles:                 0
% 2.28/0.94  gc_basic_clause_elim:                   0
% 2.28/0.94  forced_gc_time:                         0
% 2.28/0.94  parsing_time:                           0.012
% 2.28/0.94  unif_index_cands_time:                  0.
% 2.28/0.94  unif_index_add_time:                    0.
% 2.28/0.94  orderings_time:                         0.
% 2.28/0.94  out_proof_time:                         0.016
% 2.28/0.94  total_time:                             0.103
% 2.28/0.94  num_of_symbols:                         52
% 2.28/0.94  num_of_terms:                           1515
% 2.28/0.94  
% 2.28/0.94  ------ Preprocessing
% 2.28/0.94  
% 2.28/0.94  num_of_splits:                          0
% 2.28/0.94  num_of_split_atoms:                     0
% 2.28/0.94  num_of_reused_defs:                     0
% 2.28/0.94  num_eq_ax_congr_red:                    53
% 2.28/0.94  num_of_sem_filtered_clauses:            1
% 2.28/0.94  num_of_subtypes:                        0
% 2.28/0.94  monotx_restored_types:                  0
% 2.28/0.94  sat_num_of_epr_types:                   0
% 2.28/0.94  sat_num_of_non_cyclic_types:            0
% 2.28/0.94  sat_guarded_non_collapsed_types:        0
% 2.28/0.94  num_pure_diseq_elim:                    0
% 2.28/0.94  simp_replaced_by:                       0
% 2.28/0.94  res_preprocessed:                       103
% 2.28/0.94  prep_upred:                             0
% 2.28/0.94  prep_unflattend:                        18
% 2.28/0.94  smt_new_axioms:                         0
% 2.28/0.94  pred_elim_cands:                        7
% 2.28/0.94  pred_elim:                              3
% 2.28/0.94  pred_elim_cl:                           4
% 2.28/0.94  pred_elim_cycles:                       6
% 2.28/0.94  merged_defs:                            8
% 2.28/0.94  merged_defs_ncl:                        0
% 2.28/0.94  bin_hyper_res:                          8
% 2.28/0.94  prep_cycles:                            4
% 2.28/0.94  pred_elim_time:                         0.004
% 2.28/0.94  splitting_time:                         0.
% 2.28/0.94  sem_filter_time:                        0.
% 2.28/0.94  monotx_time:                            0.001
% 2.28/0.94  subtype_inf_time:                       0.
% 2.28/0.94  
% 2.28/0.94  ------ Problem properties
% 2.28/0.94  
% 2.28/0.94  clauses:                                18
% 2.28/0.94  conjectures:                            4
% 2.28/0.94  epr:                                    5
% 2.28/0.94  horn:                                   12
% 2.28/0.94  ground:                                 4
% 2.28/0.94  unary:                                  6
% 2.28/0.94  binary:                                 6
% 2.28/0.94  lits:                                   54
% 2.28/0.94  lits_eq:                                3
% 2.28/0.94  fd_pure:                                0
% 2.28/0.94  fd_pseudo:                              0
% 2.28/0.94  fd_cond:                                0
% 2.28/0.94  fd_pseudo_cond:                         0
% 2.28/0.94  ac_symbols:                             0
% 2.28/0.94  
% 2.28/0.94  ------ Propositional Solver
% 2.28/0.94  
% 2.28/0.94  prop_solver_calls:                      26
% 2.28/0.94  prop_fast_solver_calls:                 693
% 2.28/0.94  smt_solver_calls:                       0
% 2.28/0.94  smt_fast_solver_calls:                  0
% 2.28/0.94  prop_num_of_clauses:                    474
% 2.28/0.94  prop_preprocess_simplified:             3304
% 2.28/0.94  prop_fo_subsumed:                       5
% 2.28/0.94  prop_solver_time:                       0.
% 2.28/0.94  smt_solver_time:                        0.
% 2.28/0.94  smt_fast_solver_time:                   0.
% 2.28/0.94  prop_fast_solver_time:                  0.
% 2.28/0.94  prop_unsat_core_time:                   0.
% 2.28/0.94  
% 2.28/0.94  ------ QBF
% 2.28/0.94  
% 2.28/0.94  qbf_q_res:                              0
% 2.28/0.94  qbf_num_tautologies:                    0
% 2.28/0.94  qbf_prep_cycles:                        0
% 2.28/0.94  
% 2.28/0.94  ------ BMC1
% 2.28/0.94  
% 2.28/0.94  bmc1_current_bound:                     -1
% 2.28/0.94  bmc1_last_solved_bound:                 -1
% 2.28/0.94  bmc1_unsat_core_size:                   -1
% 2.28/0.94  bmc1_unsat_core_parents_size:           -1
% 2.28/0.94  bmc1_merge_next_fun:                    0
% 2.28/0.94  bmc1_unsat_core_clauses_time:           0.
% 2.28/0.94  
% 2.28/0.94  ------ Instantiation
% 2.28/0.94  
% 2.28/0.94  inst_num_of_clauses:                    136
% 2.28/0.94  inst_num_in_passive:                    59
% 2.28/0.94  inst_num_in_active:                     75
% 2.28/0.94  inst_num_in_unprocessed:                2
% 2.28/0.94  inst_num_of_loops:                      90
% 2.28/0.94  inst_num_of_learning_restarts:          0
% 2.28/0.94  inst_num_moves_active_passive:          13
% 2.28/0.94  inst_lit_activity:                      0
% 2.28/0.94  inst_lit_activity_moves:                0
% 2.28/0.94  inst_num_tautologies:                   0
% 2.28/0.94  inst_num_prop_implied:                  0
% 2.28/0.94  inst_num_existing_simplified:           0
% 2.28/0.94  inst_num_eq_res_simplified:             0
% 2.28/0.94  inst_num_child_elim:                    0
% 2.28/0.94  inst_num_of_dismatching_blockings:      9
% 2.28/0.94  inst_num_of_non_proper_insts:           73
% 2.28/0.94  inst_num_of_duplicates:                 0
% 2.28/0.94  inst_inst_num_from_inst_to_res:         0
% 2.28/0.94  inst_dismatching_checking_time:         0.
% 2.28/0.94  
% 2.28/0.94  ------ Resolution
% 2.28/0.94  
% 2.28/0.94  res_num_of_clauses:                     0
% 2.28/0.94  res_num_in_passive:                     0
% 2.28/0.94  res_num_in_active:                      0
% 2.28/0.94  res_num_of_loops:                       107
% 2.28/0.94  res_forward_subset_subsumed:            1
% 2.28/0.94  res_backward_subset_subsumed:           0
% 2.28/0.94  res_forward_subsumed:                   0
% 2.28/0.94  res_backward_subsumed:                  0
% 2.28/0.94  res_forward_subsumption_resolution:     2
% 2.28/0.94  res_backward_subsumption_resolution:    0
% 2.28/0.94  res_clause_to_clause_subsumption:       44
% 2.28/0.94  res_orphan_elimination:                 0
% 2.28/0.94  res_tautology_del:                      26
% 2.28/0.94  res_num_eq_res_simplified:              0
% 2.28/0.94  res_num_sel_changes:                    0
% 2.28/0.94  res_moves_from_active_to_pass:          0
% 2.28/0.94  
% 2.28/0.94  ------ Superposition
% 2.28/0.94  
% 2.28/0.94  sup_time_total:                         0.
% 2.28/0.94  sup_time_generating:                    0.
% 2.28/0.94  sup_time_sim_full:                      0.
% 2.28/0.94  sup_time_sim_immed:                     0.
% 2.28/0.94  
% 2.28/0.94  sup_num_of_clauses:                     25
% 2.28/0.94  sup_num_in_active:                      17
% 2.28/0.94  sup_num_in_passive:                     8
% 2.28/0.94  sup_num_of_loops:                       16
% 2.28/0.94  sup_fw_superposition:                   4
% 2.28/0.94  sup_bw_superposition:                   4
% 2.28/0.94  sup_immediate_simplified:               0
% 2.28/0.94  sup_given_eliminated:                   0
% 2.28/0.94  comparisons_done:                       0
% 2.28/0.94  comparisons_avoided:                    0
% 2.28/0.94  
% 2.28/0.94  ------ Simplifications
% 2.28/0.94  
% 2.28/0.94  
% 2.28/0.94  sim_fw_subset_subsumed:                 0
% 2.28/0.94  sim_bw_subset_subsumed:                 0
% 2.28/0.94  sim_fw_subsumed:                        0
% 2.28/0.94  sim_bw_subsumed:                        0
% 2.28/0.94  sim_fw_subsumption_res:                 0
% 2.28/0.94  sim_bw_subsumption_res:                 0
% 2.28/0.94  sim_tautology_del:                      0
% 2.28/0.94  sim_eq_tautology_del:                   0
% 2.28/0.94  sim_eq_res_simp:                        0
% 2.28/0.94  sim_fw_demodulated:                     0
% 2.28/0.94  sim_bw_demodulated:                     0
% 2.28/0.94  sim_light_normalised:                   0
% 2.28/0.94  sim_joinable_taut:                      0
% 2.28/0.94  sim_joinable_simp:                      0
% 2.28/0.94  sim_ac_normalised:                      0
% 2.28/0.94  sim_smt_subsumption:                    0
% 2.28/0.94  
%------------------------------------------------------------------------------
