%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:11 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 170 expanded)
%              Number of clauses        :   44 (  54 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :   16
%              Number of atoms          :  405 ( 826 expanded)
%              Number of equality atoms :   73 ( 107 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f4,f32])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_waybel_0(X0,sK6,u1_struct_0(X0))
        & l1_waybel_0(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK5,X1,u1_struct_0(sK5))
          & l1_waybel_0(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ~ r1_waybel_0(sK5,sK6,u1_struct_0(sK5))
    & l1_waybel_0(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_struct_0(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f24,f41,f40])).

fof(f68,plain,(
    ~ r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f37,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK4(X0,X1,X2,X5))
        & m1_subset_1(sK4(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK3(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK3(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK4(X0,X1,X2,X5))
                      & m1_subset_1(sK4(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f37,f36])).

fof(f57,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1204,plain,
    ( k6_subset_1(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2100,plain,
    ( k6_subset_1(X0,X1) = X0
    | r2_hidden(sK1(X0,X1,X0),X0) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1204])).

cnf(c_2102,plain,
    ( k6_subset_1(X0,X1) = X0
    | r2_hidden(sK1(X0,X1,X0),X0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2100])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1206,plain,
    ( k6_subset_1(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2406,plain,
    ( k6_subset_1(X0,X1) = X0
    | r2_hidden(sK1(X0,X1,X0),X0) != iProver_top
    | r2_hidden(sK1(X0,X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2102,c_1206])).

cnf(c_2424,plain,
    ( k6_subset_1(X0,X1) = X0
    | r2_hidden(sK1(X0,X1,X0),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2406,c_2102])).

cnf(c_9,plain,
    ( m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1200,plain,
    ( m1_subset_1(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_271,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X1,X0) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_1187,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_1498,plain,
    ( r2_hidden(X0,sK2(k1_zfmisc_1(k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_1187])).

cnf(c_2767,plain,
    ( k6_subset_1(X0,sK2(k1_zfmisc_1(k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_2424,c_1498])).

cnf(c_16,plain,
    ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1196,plain,
    ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) = iProver_top
    | r2_waybel_0(X0,X1,X2) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2892,plain,
    ( r1_waybel_0(X0,X1,u1_struct_0(X0)) = iProver_top
    | r2_waybel_0(X0,X1,sK2(k1_zfmisc_1(k1_xboole_0))) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2767,c_1196])).

cnf(c_20,negated_conjecture,
    ( ~ r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1192,plain,
    ( r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14578,plain,
    ( r2_waybel_0(sK5,sK6,sK2(k1_zfmisc_1(k1_xboole_0))) = iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2892,c_1192])).

cnf(c_1478,plain,
    ( ~ m1_subset_1(sK2(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X0,sK2(k1_zfmisc_1(k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_2986,plain,
    ( ~ m1_subset_1(sK2(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,sK2(k1_zfmisc_1(k1_xboole_0)),sK2(u1_struct_0(sK6)))),sK2(k1_zfmisc_1(k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_1478])).

cnf(c_2989,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,sK2(k1_zfmisc_1(k1_xboole_0)),sK2(u1_struct_0(sK6)))),sK2(k1_zfmisc_1(k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2986])).

cnf(c_13,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1466,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ l1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,X1)),X0)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1585,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ l1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,sK2(u1_struct_0(sK6)))),X0)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1466])).

cnf(c_2985,plain,
    ( ~ r2_waybel_0(sK5,sK6,sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,sK2(k1_zfmisc_1(k1_xboole_0)),sK2(u1_struct_0(sK6)))),sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1585])).

cnf(c_2987,plain,
    ( r2_waybel_0(sK5,sK6,sK2(k1_zfmisc_1(k1_xboole_0))) != iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,sK2(k1_zfmisc_1(k1_xboole_0)),sK2(u1_struct_0(sK6)))),sK2(k1_zfmisc_1(k1_xboole_0))) = iProver_top
    | l1_struct_0(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2985])).

cnf(c_1529,plain,
    ( m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1534,plain,
    ( m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1529])).

cnf(c_1479,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1484,plain,
    ( m1_subset_1(sK2(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1479])).

cnf(c_21,negated_conjecture,
    ( l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,plain,
    ( l1_waybel_0(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_27,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,plain,
    ( l1_struct_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14578,c_2989,c_2987,c_1534,c_1484,c_28,c_27,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : iproveropt_run.sh %d %s
% 0.07/0.27  % Computer   : n012.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 16:49:22 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.27  % Running in FOF mode
% 3.68/0.86  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/0.86  
% 3.68/0.86  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/0.86  
% 3.68/0.86  ------  iProver source info
% 3.68/0.86  
% 3.68/0.86  git: date: 2020-06-30 10:37:57 +0100
% 3.68/0.86  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/0.86  git: non_committed_changes: false
% 3.68/0.86  git: last_make_outside_of_git: false
% 3.68/0.86  
% 3.68/0.86  ------ 
% 3.68/0.86  
% 3.68/0.86  ------ Input Options
% 3.68/0.86  
% 3.68/0.86  --out_options                           all
% 3.68/0.86  --tptp_safe_out                         true
% 3.68/0.86  --problem_path                          ""
% 3.68/0.86  --include_path                          ""
% 3.68/0.86  --clausifier                            res/vclausify_rel
% 3.68/0.86  --clausifier_options                    --mode clausify
% 3.68/0.86  --stdin                                 false
% 3.68/0.86  --stats_out                             all
% 3.68/0.86  
% 3.68/0.86  ------ General Options
% 3.68/0.86  
% 3.68/0.86  --fof                                   false
% 3.68/0.86  --time_out_real                         305.
% 3.68/0.86  --time_out_virtual                      -1.
% 3.68/0.86  --symbol_type_check                     false
% 3.68/0.86  --clausify_out                          false
% 3.68/0.86  --sig_cnt_out                           false
% 3.68/0.86  --trig_cnt_out                          false
% 3.68/0.86  --trig_cnt_out_tolerance                1.
% 3.68/0.86  --trig_cnt_out_sk_spl                   false
% 3.68/0.86  --abstr_cl_out                          false
% 3.68/0.86  
% 3.68/0.86  ------ Global Options
% 3.68/0.86  
% 3.68/0.86  --schedule                              default
% 3.68/0.86  --add_important_lit                     false
% 3.68/0.86  --prop_solver_per_cl                    1000
% 3.68/0.86  --min_unsat_core                        false
% 3.68/0.86  --soft_assumptions                      false
% 3.68/0.86  --soft_lemma_size                       3
% 3.68/0.86  --prop_impl_unit_size                   0
% 3.68/0.86  --prop_impl_unit                        []
% 3.68/0.86  --share_sel_clauses                     true
% 3.68/0.86  --reset_solvers                         false
% 3.68/0.86  --bc_imp_inh                            [conj_cone]
% 3.68/0.86  --conj_cone_tolerance                   3.
% 3.68/0.86  --extra_neg_conj                        none
% 3.68/0.86  --large_theory_mode                     true
% 3.68/0.86  --prolific_symb_bound                   200
% 3.68/0.86  --lt_threshold                          2000
% 3.68/0.86  --clause_weak_htbl                      true
% 3.68/0.86  --gc_record_bc_elim                     false
% 3.68/0.86  
% 3.68/0.86  ------ Preprocessing Options
% 3.68/0.86  
% 3.68/0.86  --preprocessing_flag                    true
% 3.68/0.86  --time_out_prep_mult                    0.1
% 3.68/0.86  --splitting_mode                        input
% 3.68/0.86  --splitting_grd                         true
% 3.68/0.86  --splitting_cvd                         false
% 3.68/0.86  --splitting_cvd_svl                     false
% 3.68/0.86  --splitting_nvd                         32
% 3.68/0.86  --sub_typing                            true
% 3.68/0.86  --prep_gs_sim                           true
% 3.68/0.86  --prep_unflatten                        true
% 3.68/0.86  --prep_res_sim                          true
% 3.68/0.86  --prep_upred                            true
% 3.68/0.86  --prep_sem_filter                       exhaustive
% 3.68/0.86  --prep_sem_filter_out                   false
% 3.68/0.86  --pred_elim                             true
% 3.68/0.86  --res_sim_input                         true
% 3.68/0.86  --eq_ax_congr_red                       true
% 3.68/0.86  --pure_diseq_elim                       true
% 3.68/0.86  --brand_transform                       false
% 3.68/0.86  --non_eq_to_eq                          false
% 3.68/0.86  --prep_def_merge                        true
% 3.68/0.86  --prep_def_merge_prop_impl              false
% 3.68/0.86  --prep_def_merge_mbd                    true
% 3.68/0.86  --prep_def_merge_tr_red                 false
% 3.68/0.86  --prep_def_merge_tr_cl                  false
% 3.68/0.86  --smt_preprocessing                     true
% 3.68/0.86  --smt_ac_axioms                         fast
% 3.68/0.86  --preprocessed_out                      false
% 3.68/0.86  --preprocessed_stats                    false
% 3.68/0.86  
% 3.68/0.86  ------ Abstraction refinement Options
% 3.68/0.86  
% 3.68/0.86  --abstr_ref                             []
% 3.68/0.86  --abstr_ref_prep                        false
% 3.68/0.86  --abstr_ref_until_sat                   false
% 3.68/0.86  --abstr_ref_sig_restrict                funpre
% 3.68/0.86  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.86  --abstr_ref_under                       []
% 3.68/0.86  
% 3.68/0.86  ------ SAT Options
% 3.68/0.86  
% 3.68/0.86  --sat_mode                              false
% 3.68/0.86  --sat_fm_restart_options                ""
% 3.68/0.86  --sat_gr_def                            false
% 3.68/0.86  --sat_epr_types                         true
% 3.68/0.86  --sat_non_cyclic_types                  false
% 3.68/0.86  --sat_finite_models                     false
% 3.68/0.86  --sat_fm_lemmas                         false
% 3.68/0.86  --sat_fm_prep                           false
% 3.68/0.86  --sat_fm_uc_incr                        true
% 3.68/0.86  --sat_out_model                         small
% 3.68/0.86  --sat_out_clauses                       false
% 3.68/0.86  
% 3.68/0.86  ------ QBF Options
% 3.68/0.86  
% 3.68/0.86  --qbf_mode                              false
% 3.68/0.86  --qbf_elim_univ                         false
% 3.68/0.86  --qbf_dom_inst                          none
% 3.68/0.86  --qbf_dom_pre_inst                      false
% 3.68/0.86  --qbf_sk_in                             false
% 3.68/0.86  --qbf_pred_elim                         true
% 3.68/0.86  --qbf_split                             512
% 3.68/0.86  
% 3.68/0.86  ------ BMC1 Options
% 3.68/0.86  
% 3.68/0.86  --bmc1_incremental                      false
% 3.68/0.86  --bmc1_axioms                           reachable_all
% 3.68/0.86  --bmc1_min_bound                        0
% 3.68/0.86  --bmc1_max_bound                        -1
% 3.68/0.86  --bmc1_max_bound_default                -1
% 3.68/0.86  --bmc1_symbol_reachability              true
% 3.68/0.86  --bmc1_property_lemmas                  false
% 3.68/0.86  --bmc1_k_induction                      false
% 3.68/0.86  --bmc1_non_equiv_states                 false
% 3.68/0.86  --bmc1_deadlock                         false
% 3.68/0.86  --bmc1_ucm                              false
% 3.68/0.86  --bmc1_add_unsat_core                   none
% 3.68/0.86  --bmc1_unsat_core_children              false
% 3.68/0.86  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.86  --bmc1_out_stat                         full
% 3.68/0.86  --bmc1_ground_init                      false
% 3.68/0.86  --bmc1_pre_inst_next_state              false
% 3.68/0.86  --bmc1_pre_inst_state                   false
% 3.68/0.86  --bmc1_pre_inst_reach_state             false
% 3.68/0.86  --bmc1_out_unsat_core                   false
% 3.68/0.86  --bmc1_aig_witness_out                  false
% 3.68/0.86  --bmc1_verbose                          false
% 3.68/0.86  --bmc1_dump_clauses_tptp                false
% 3.68/0.86  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.86  --bmc1_dump_file                        -
% 3.68/0.86  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.86  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.86  --bmc1_ucm_extend_mode                  1
% 3.68/0.86  --bmc1_ucm_init_mode                    2
% 3.68/0.86  --bmc1_ucm_cone_mode                    none
% 3.68/0.86  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.86  --bmc1_ucm_relax_model                  4
% 3.68/0.86  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.86  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.86  --bmc1_ucm_layered_model                none
% 3.68/0.86  --bmc1_ucm_max_lemma_size               10
% 3.68/0.86  
% 3.68/0.86  ------ AIG Options
% 3.68/0.86  
% 3.68/0.86  --aig_mode                              false
% 3.68/0.86  
% 3.68/0.86  ------ Instantiation Options
% 3.68/0.86  
% 3.68/0.86  --instantiation_flag                    true
% 3.68/0.86  --inst_sos_flag                         false
% 3.68/0.86  --inst_sos_phase                        true
% 3.68/0.86  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.86  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.86  --inst_lit_sel_side                     num_symb
% 3.68/0.86  --inst_solver_per_active                1400
% 3.68/0.86  --inst_solver_calls_frac                1.
% 3.68/0.86  --inst_passive_queue_type               priority_queues
% 3.68/0.86  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.86  --inst_passive_queues_freq              [25;2]
% 3.68/0.86  --inst_dismatching                      true
% 3.68/0.86  --inst_eager_unprocessed_to_passive     true
% 3.68/0.86  --inst_prop_sim_given                   true
% 3.68/0.86  --inst_prop_sim_new                     false
% 3.68/0.86  --inst_subs_new                         false
% 3.68/0.86  --inst_eq_res_simp                      false
% 3.68/0.86  --inst_subs_given                       false
% 3.68/0.86  --inst_orphan_elimination               true
% 3.68/0.86  --inst_learning_loop_flag               true
% 3.68/0.86  --inst_learning_start                   3000
% 3.68/0.86  --inst_learning_factor                  2
% 3.68/0.86  --inst_start_prop_sim_after_learn       3
% 3.68/0.86  --inst_sel_renew                        solver
% 3.68/0.86  --inst_lit_activity_flag                true
% 3.68/0.86  --inst_restr_to_given                   false
% 3.68/0.86  --inst_activity_threshold               500
% 3.68/0.86  --inst_out_proof                        true
% 3.68/0.86  
% 3.68/0.86  ------ Resolution Options
% 3.68/0.86  
% 3.68/0.86  --resolution_flag                       true
% 3.68/0.86  --res_lit_sel                           adaptive
% 3.68/0.86  --res_lit_sel_side                      none
% 3.68/0.86  --res_ordering                          kbo
% 3.68/0.86  --res_to_prop_solver                    active
% 3.68/0.86  --res_prop_simpl_new                    false
% 3.68/0.86  --res_prop_simpl_given                  true
% 3.68/0.86  --res_passive_queue_type                priority_queues
% 3.68/0.86  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.86  --res_passive_queues_freq               [15;5]
% 3.68/0.86  --res_forward_subs                      full
% 3.68/0.86  --res_backward_subs                     full
% 3.68/0.86  --res_forward_subs_resolution           true
% 3.68/0.86  --res_backward_subs_resolution          true
% 3.68/0.86  --res_orphan_elimination                true
% 3.68/0.86  --res_time_limit                        2.
% 3.68/0.86  --res_out_proof                         true
% 3.68/0.86  
% 3.68/0.86  ------ Superposition Options
% 3.68/0.86  
% 3.68/0.86  --superposition_flag                    true
% 3.68/0.86  --sup_passive_queue_type                priority_queues
% 3.68/0.86  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.86  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.86  --demod_completeness_check              fast
% 3.68/0.86  --demod_use_ground                      true
% 3.68/0.86  --sup_to_prop_solver                    passive
% 3.68/0.86  --sup_prop_simpl_new                    true
% 3.68/0.86  --sup_prop_simpl_given                  true
% 3.68/0.86  --sup_fun_splitting                     false
% 3.68/0.86  --sup_smt_interval                      50000
% 3.68/0.86  
% 3.68/0.86  ------ Superposition Simplification Setup
% 3.68/0.86  
% 3.68/0.86  --sup_indices_passive                   []
% 3.68/0.86  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.86  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.86  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.86  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.86  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.86  --sup_full_bw                           [BwDemod]
% 3.68/0.86  --sup_immed_triv                        [TrivRules]
% 3.68/0.86  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.86  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.86  --sup_immed_bw_main                     []
% 3.68/0.86  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.68/0.86  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.86  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.86  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.68/0.86  
% 3.68/0.86  ------ Combination Options
% 3.68/0.86  
% 3.68/0.86  --comb_res_mult                         3
% 3.68/0.86  --comb_sup_mult                         2
% 3.68/0.86  --comb_inst_mult                        10
% 3.68/0.86  
% 3.68/0.86  ------ Debug Options
% 3.68/0.86  
% 3.68/0.86  --dbg_backtrace                         false
% 3.68/0.86  --dbg_dump_prop_clauses                 false
% 3.68/0.86  --dbg_dump_prop_clauses_file            -
% 3.68/0.86  --dbg_out_stat                          false
% 3.68/0.86  ------ Parsing...
% 3.68/0.86  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/0.86  
% 3.68/0.86  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.68/0.86  
% 3.68/0.86  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/0.86  
% 3.68/0.86  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.86  ------ Proving...
% 3.68/0.86  ------ Problem Properties 
% 3.68/0.86  
% 3.68/0.86  
% 3.68/0.86  clauses                                 23
% 3.68/0.86  conjectures                             5
% 3.68/0.86  EPR                                     6
% 3.68/0.86  Horn                                    10
% 3.68/0.86  unary                                   6
% 3.68/0.86  binary                                  5
% 3.68/0.86  lits                                    85
% 3.68/0.86  lits eq                                 3
% 3.68/0.86  fd_pure                                 0
% 3.68/0.86  fd_pseudo                               0
% 3.68/0.86  fd_cond                                 0
% 3.68/0.86  fd_pseudo_cond                          3
% 3.68/0.86  AC symbols                              0
% 3.68/0.86  
% 3.68/0.86  ------ Schedule dynamic 5 is on 
% 3.68/0.86  
% 3.68/0.86  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.68/0.86  
% 3.68/0.86  
% 3.68/0.86  ------ 
% 3.68/0.86  Current options:
% 3.68/0.86  ------ 
% 3.68/0.86  
% 3.68/0.86  ------ Input Options
% 3.68/0.86  
% 3.68/0.86  --out_options                           all
% 3.68/0.86  --tptp_safe_out                         true
% 3.68/0.86  --problem_path                          ""
% 3.68/0.86  --include_path                          ""
% 3.68/0.86  --clausifier                            res/vclausify_rel
% 3.68/0.86  --clausifier_options                    --mode clausify
% 3.68/0.86  --stdin                                 false
% 3.68/0.86  --stats_out                             all
% 3.68/0.86  
% 3.68/0.86  ------ General Options
% 3.68/0.86  
% 3.68/0.86  --fof                                   false
% 3.68/0.86  --time_out_real                         305.
% 3.68/0.86  --time_out_virtual                      -1.
% 3.68/0.86  --symbol_type_check                     false
% 3.68/0.86  --clausify_out                          false
% 3.68/0.86  --sig_cnt_out                           false
% 3.68/0.86  --trig_cnt_out                          false
% 3.68/0.86  --trig_cnt_out_tolerance                1.
% 3.68/0.86  --trig_cnt_out_sk_spl                   false
% 3.68/0.86  --abstr_cl_out                          false
% 3.68/0.86  
% 3.68/0.86  ------ Global Options
% 3.68/0.86  
% 3.68/0.86  --schedule                              default
% 3.68/0.86  --add_important_lit                     false
% 3.68/0.86  --prop_solver_per_cl                    1000
% 3.68/0.86  --min_unsat_core                        false
% 3.68/0.86  --soft_assumptions                      false
% 3.68/0.86  --soft_lemma_size                       3
% 3.68/0.86  --prop_impl_unit_size                   0
% 3.68/0.86  --prop_impl_unit                        []
% 3.68/0.86  --share_sel_clauses                     true
% 3.68/0.86  --reset_solvers                         false
% 3.68/0.86  --bc_imp_inh                            [conj_cone]
% 3.68/0.86  --conj_cone_tolerance                   3.
% 3.68/0.86  --extra_neg_conj                        none
% 3.68/0.86  --large_theory_mode                     true
% 3.68/0.86  --prolific_symb_bound                   200
% 3.68/0.86  --lt_threshold                          2000
% 3.68/0.86  --clause_weak_htbl                      true
% 3.68/0.86  --gc_record_bc_elim                     false
% 3.68/0.86  
% 3.68/0.86  ------ Preprocessing Options
% 3.68/0.86  
% 3.68/0.86  --preprocessing_flag                    true
% 3.68/0.86  --time_out_prep_mult                    0.1
% 3.68/0.86  --splitting_mode                        input
% 3.68/0.86  --splitting_grd                         true
% 3.68/0.86  --splitting_cvd                         false
% 3.68/0.86  --splitting_cvd_svl                     false
% 3.68/0.86  --splitting_nvd                         32
% 3.68/0.86  --sub_typing                            true
% 3.68/0.86  --prep_gs_sim                           true
% 3.68/0.86  --prep_unflatten                        true
% 3.68/0.86  --prep_res_sim                          true
% 3.68/0.86  --prep_upred                            true
% 3.68/0.86  --prep_sem_filter                       exhaustive
% 3.68/0.86  --prep_sem_filter_out                   false
% 3.68/0.86  --pred_elim                             true
% 3.68/0.86  --res_sim_input                         true
% 3.68/0.86  --eq_ax_congr_red                       true
% 3.68/0.86  --pure_diseq_elim                       true
% 3.68/0.86  --brand_transform                       false
% 3.68/0.86  --non_eq_to_eq                          false
% 3.68/0.86  --prep_def_merge                        true
% 3.68/0.86  --prep_def_merge_prop_impl              false
% 3.68/0.86  --prep_def_merge_mbd                    true
% 3.68/0.86  --prep_def_merge_tr_red                 false
% 3.68/0.86  --prep_def_merge_tr_cl                  false
% 3.68/0.86  --smt_preprocessing                     true
% 3.68/0.86  --smt_ac_axioms                         fast
% 3.68/0.86  --preprocessed_out                      false
% 3.68/0.86  --preprocessed_stats                    false
% 3.68/0.86  
% 3.68/0.86  ------ Abstraction refinement Options
% 3.68/0.86  
% 3.68/0.86  --abstr_ref                             []
% 3.68/0.86  --abstr_ref_prep                        false
% 3.68/0.86  --abstr_ref_until_sat                   false
% 3.68/0.86  --abstr_ref_sig_restrict                funpre
% 3.68/0.86  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.86  --abstr_ref_under                       []
% 3.68/0.86  
% 3.68/0.86  ------ SAT Options
% 3.68/0.86  
% 3.68/0.86  --sat_mode                              false
% 3.68/0.86  --sat_fm_restart_options                ""
% 3.68/0.86  --sat_gr_def                            false
% 3.68/0.86  --sat_epr_types                         true
% 3.68/0.86  --sat_non_cyclic_types                  false
% 3.68/0.86  --sat_finite_models                     false
% 3.68/0.86  --sat_fm_lemmas                         false
% 3.68/0.86  --sat_fm_prep                           false
% 3.68/0.86  --sat_fm_uc_incr                        true
% 3.68/0.86  --sat_out_model                         small
% 3.68/0.86  --sat_out_clauses                       false
% 3.68/0.86  
% 3.68/0.86  ------ QBF Options
% 3.68/0.86  
% 3.68/0.86  --qbf_mode                              false
% 3.68/0.86  --qbf_elim_univ                         false
% 3.68/0.86  --qbf_dom_inst                          none
% 3.68/0.86  --qbf_dom_pre_inst                      false
% 3.68/0.86  --qbf_sk_in                             false
% 3.68/0.86  --qbf_pred_elim                         true
% 3.68/0.86  --qbf_split                             512
% 3.68/0.86  
% 3.68/0.86  ------ BMC1 Options
% 3.68/0.86  
% 3.68/0.86  --bmc1_incremental                      false
% 3.68/0.86  --bmc1_axioms                           reachable_all
% 3.68/0.86  --bmc1_min_bound                        0
% 3.68/0.86  --bmc1_max_bound                        -1
% 3.68/0.86  --bmc1_max_bound_default                -1
% 3.68/0.86  --bmc1_symbol_reachability              true
% 3.68/0.86  --bmc1_property_lemmas                  false
% 3.68/0.86  --bmc1_k_induction                      false
% 3.68/0.86  --bmc1_non_equiv_states                 false
% 3.68/0.86  --bmc1_deadlock                         false
% 3.68/0.86  --bmc1_ucm                              false
% 3.68/0.86  --bmc1_add_unsat_core                   none
% 3.68/0.86  --bmc1_unsat_core_children              false
% 3.68/0.86  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.86  --bmc1_out_stat                         full
% 3.68/0.86  --bmc1_ground_init                      false
% 3.68/0.86  --bmc1_pre_inst_next_state              false
% 3.68/0.86  --bmc1_pre_inst_state                   false
% 3.68/0.86  --bmc1_pre_inst_reach_state             false
% 3.68/0.86  --bmc1_out_unsat_core                   false
% 3.68/0.86  --bmc1_aig_witness_out                  false
% 3.68/0.86  --bmc1_verbose                          false
% 3.68/0.86  --bmc1_dump_clauses_tptp                false
% 3.68/0.86  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.86  --bmc1_dump_file                        -
% 3.68/0.86  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.86  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.86  --bmc1_ucm_extend_mode                  1
% 3.68/0.86  --bmc1_ucm_init_mode                    2
% 3.68/0.86  --bmc1_ucm_cone_mode                    none
% 3.68/0.86  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.86  --bmc1_ucm_relax_model                  4
% 3.68/0.86  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.86  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.86  --bmc1_ucm_layered_model                none
% 3.68/0.86  --bmc1_ucm_max_lemma_size               10
% 3.68/0.86  
% 3.68/0.86  ------ AIG Options
% 3.68/0.86  
% 3.68/0.86  --aig_mode                              false
% 3.68/0.86  
% 3.68/0.86  ------ Instantiation Options
% 3.68/0.86  
% 3.68/0.86  --instantiation_flag                    true
% 3.68/0.86  --inst_sos_flag                         false
% 3.68/0.86  --inst_sos_phase                        true
% 3.68/0.86  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.86  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.86  --inst_lit_sel_side                     none
% 3.68/0.86  --inst_solver_per_active                1400
% 3.68/0.86  --inst_solver_calls_frac                1.
% 3.68/0.86  --inst_passive_queue_type               priority_queues
% 3.68/0.86  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.86  --inst_passive_queues_freq              [25;2]
% 3.68/0.86  --inst_dismatching                      true
% 3.68/0.86  --inst_eager_unprocessed_to_passive     true
% 3.68/0.86  --inst_prop_sim_given                   true
% 3.68/0.86  --inst_prop_sim_new                     false
% 3.68/0.86  --inst_subs_new                         false
% 3.68/0.86  --inst_eq_res_simp                      false
% 3.68/0.86  --inst_subs_given                       false
% 3.68/0.86  --inst_orphan_elimination               true
% 3.68/0.86  --inst_learning_loop_flag               true
% 3.68/0.86  --inst_learning_start                   3000
% 3.68/0.86  --inst_learning_factor                  2
% 3.68/0.86  --inst_start_prop_sim_after_learn       3
% 3.68/0.86  --inst_sel_renew                        solver
% 3.68/0.86  --inst_lit_activity_flag                true
% 3.68/0.86  --inst_restr_to_given                   false
% 3.68/0.86  --inst_activity_threshold               500
% 3.68/0.86  --inst_out_proof                        true
% 3.68/0.86  
% 3.68/0.86  ------ Resolution Options
% 3.68/0.86  
% 3.68/0.86  --resolution_flag                       false
% 3.68/0.86  --res_lit_sel                           adaptive
% 3.68/0.86  --res_lit_sel_side                      none
% 3.68/0.86  --res_ordering                          kbo
% 3.68/0.86  --res_to_prop_solver                    active
% 3.68/0.86  --res_prop_simpl_new                    false
% 3.68/0.86  --res_prop_simpl_given                  true
% 3.68/0.86  --res_passive_queue_type                priority_queues
% 3.68/0.86  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.86  --res_passive_queues_freq               [15;5]
% 3.68/0.86  --res_forward_subs                      full
% 3.68/0.86  --res_backward_subs                     full
% 3.68/0.86  --res_forward_subs_resolution           true
% 3.68/0.86  --res_backward_subs_resolution          true
% 3.68/0.86  --res_orphan_elimination                true
% 3.68/0.86  --res_time_limit                        2.
% 3.68/0.86  --res_out_proof                         true
% 3.68/0.86  
% 3.68/0.86  ------ Superposition Options
% 3.68/0.86  
% 3.68/0.86  --superposition_flag                    true
% 3.68/0.86  --sup_passive_queue_type                priority_queues
% 3.68/0.86  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.86  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.86  --demod_completeness_check              fast
% 3.68/0.86  --demod_use_ground                      true
% 3.68/0.86  --sup_to_prop_solver                    passive
% 3.68/0.86  --sup_prop_simpl_new                    true
% 3.68/0.86  --sup_prop_simpl_given                  true
% 3.68/0.86  --sup_fun_splitting                     false
% 3.68/0.86  --sup_smt_interval                      50000
% 3.68/0.86  
% 3.68/0.86  ------ Superposition Simplification Setup
% 3.68/0.86  
% 3.68/0.86  --sup_indices_passive                   []
% 3.68/0.86  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.86  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.86  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.86  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.86  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.86  --sup_full_bw                           [BwDemod]
% 3.68/0.86  --sup_immed_triv                        [TrivRules]
% 3.68/0.86  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.86  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.86  --sup_immed_bw_main                     []
% 3.68/0.86  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.68/0.86  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.86  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.86  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.68/0.86  
% 3.68/0.86  ------ Combination Options
% 3.68/0.86  
% 3.68/0.86  --comb_res_mult                         3
% 3.68/0.86  --comb_sup_mult                         2
% 3.68/0.86  --comb_inst_mult                        10
% 3.68/0.86  
% 3.68/0.86  ------ Debug Options
% 3.68/0.86  
% 3.68/0.86  --dbg_backtrace                         false
% 3.68/0.86  --dbg_dump_prop_clauses                 false
% 3.68/0.86  --dbg_dump_prop_clauses_file            -
% 3.68/0.86  --dbg_out_stat                          false
% 3.68/0.86  
% 3.68/0.86  
% 3.68/0.86  
% 3.68/0.86  
% 3.68/0.86  ------ Proving...
% 3.68/0.86  
% 3.68/0.86  
% 3.68/0.86  % SZS status Theorem for theBenchmark.p
% 3.68/0.86  
% 3.68/0.86  % SZS output start CNFRefutation for theBenchmark.p
% 3.68/0.86  
% 3.68/0.86  fof(f2,axiom,(
% 3.68/0.86    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.86  
% 3.68/0.86  fof(f27,plain,(
% 3.68/0.86    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.68/0.86    inference(nnf_transformation,[],[f2])).
% 3.68/0.86  
% 3.68/0.86  fof(f28,plain,(
% 3.68/0.86    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.68/0.86    inference(flattening,[],[f27])).
% 3.68/0.86  
% 3.68/0.86  fof(f29,plain,(
% 3.68/0.86    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.68/0.86    inference(rectify,[],[f28])).
% 3.68/0.86  
% 3.68/0.86  fof(f30,plain,(
% 3.68/0.86    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.68/0.86    introduced(choice_axiom,[])).
% 3.68/0.86  
% 3.68/0.86  fof(f31,plain,(
% 3.68/0.86    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.68/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 3.68/0.86  
% 3.68/0.86  fof(f48,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f31])).
% 3.68/0.86  
% 3.68/0.86  fof(f5,axiom,(
% 3.68/0.86    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.86  
% 3.68/0.86  fof(f53,plain,(
% 3.68/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f5])).
% 3.68/0.86  
% 3.68/0.86  fof(f71,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (k6_subset_1(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.68/0.86    inference(definition_unfolding,[],[f48,f53])).
% 3.68/0.86  
% 3.68/0.86  fof(f50,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f31])).
% 3.68/0.86  
% 3.68/0.86  fof(f69,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (k6_subset_1(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.68/0.86    inference(definition_unfolding,[],[f50,f53])).
% 3.68/0.86  
% 3.68/0.86  fof(f4,axiom,(
% 3.68/0.86    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.86  
% 3.68/0.86  fof(f32,plain,(
% 3.68/0.86    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK2(X0),X0))),
% 3.68/0.86    introduced(choice_axiom,[])).
% 3.68/0.86  
% 3.68/0.86  fof(f33,plain,(
% 3.68/0.86    ! [X0] : m1_subset_1(sK2(X0),X0)),
% 3.68/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f4,f32])).
% 3.68/0.86  
% 3.68/0.86  fof(f52,plain,(
% 3.68/0.86    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f33])).
% 3.68/0.86  
% 3.68/0.86  fof(f3,axiom,(
% 3.68/0.86    v1_xboole_0(k1_xboole_0)),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.86  
% 3.68/0.86  fof(f51,plain,(
% 3.68/0.86    v1_xboole_0(k1_xboole_0)),
% 3.68/0.86    inference(cnf_transformation,[],[f3])).
% 3.68/0.86  
% 3.68/0.86  fof(f6,axiom,(
% 3.68/0.86    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.86  
% 3.68/0.86  fof(f16,plain,(
% 3.68/0.86    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.68/0.86    inference(ennf_transformation,[],[f6])).
% 3.68/0.86  
% 3.68/0.86  fof(f54,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f16])).
% 3.68/0.86  
% 3.68/0.86  fof(f8,axiom,(
% 3.68/0.86    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.86  
% 3.68/0.86  fof(f19,plain,(
% 3.68/0.86    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.68/0.86    inference(ennf_transformation,[],[f8])).
% 3.68/0.86  
% 3.68/0.86  fof(f20,plain,(
% 3.68/0.86    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.68/0.86    inference(flattening,[],[f19])).
% 3.68/0.86  
% 3.68/0.86  fof(f39,plain,(
% 3.68/0.86    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.68/0.86    inference(nnf_transformation,[],[f20])).
% 3.68/0.86  
% 3.68/0.86  fof(f61,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f39])).
% 3.68/0.86  
% 3.68/0.86  fof(f10,conjecture,(
% 3.68/0.86    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.86  
% 3.68/0.86  fof(f11,negated_conjecture,(
% 3.68/0.86    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.68/0.86    inference(negated_conjecture,[],[f10])).
% 3.68/0.86  
% 3.68/0.86  fof(f13,plain,(
% 3.68/0.86    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.68/0.86    inference(pure_predicate_removal,[],[f11])).
% 3.68/0.86  
% 3.68/0.86  fof(f14,plain,(
% 3.68/0.86    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.68/0.86    inference(pure_predicate_removal,[],[f13])).
% 3.68/0.86  
% 3.68/0.86  fof(f23,plain,(
% 3.68/0.86    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 3.68/0.86    inference(ennf_transformation,[],[f14])).
% 3.68/0.86  
% 3.68/0.86  fof(f24,plain,(
% 3.68/0.86    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 3.68/0.86    inference(flattening,[],[f23])).
% 3.68/0.86  
% 3.68/0.86  fof(f41,plain,(
% 3.68/0.86    ( ! [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (~r1_waybel_0(X0,sK6,u1_struct_0(X0)) & l1_waybel_0(sK6,X0) & ~v2_struct_0(sK6))) )),
% 3.68/0.86    introduced(choice_axiom,[])).
% 3.68/0.86  
% 3.68/0.86  fof(f40,plain,(
% 3.68/0.86    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK5,X1,u1_struct_0(sK5)) & l1_waybel_0(X1,sK5) & ~v2_struct_0(X1)) & l1_struct_0(sK5) & ~v2_struct_0(sK5))),
% 3.68/0.86    introduced(choice_axiom,[])).
% 3.68/0.86  
% 3.68/0.86  fof(f42,plain,(
% 3.68/0.86    (~r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) & l1_waybel_0(sK6,sK5) & ~v2_struct_0(sK6)) & l1_struct_0(sK5) & ~v2_struct_0(sK5)),
% 3.68/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f24,f41,f40])).
% 3.68/0.86  
% 3.68/0.86  fof(f68,plain,(
% 3.68/0.86    ~r1_waybel_0(sK5,sK6,u1_struct_0(sK5))),
% 3.68/0.86    inference(cnf_transformation,[],[f42])).
% 3.68/0.86  
% 3.68/0.86  fof(f7,axiom,(
% 3.68/0.86    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 3.68/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.86  
% 3.68/0.86  fof(f17,plain,(
% 3.68/0.86    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.68/0.86    inference(ennf_transformation,[],[f7])).
% 3.68/0.86  
% 3.68/0.86  fof(f18,plain,(
% 3.68/0.86    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.68/0.86    inference(flattening,[],[f17])).
% 3.68/0.86  
% 3.68/0.86  fof(f34,plain,(
% 3.68/0.86    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.68/0.86    inference(nnf_transformation,[],[f18])).
% 3.68/0.86  
% 3.68/0.86  fof(f35,plain,(
% 3.68/0.86    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.68/0.86    inference(rectify,[],[f34])).
% 3.68/0.86  
% 3.68/0.86  fof(f37,plain,(
% 3.68/0.86    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK4(X0,X1,X2,X5)) & m1_subset_1(sK4(X0,X1,X2,X5),u1_struct_0(X1))))),
% 3.68/0.86    introduced(choice_axiom,[])).
% 3.68/0.86  
% 3.68/0.86  fof(f36,plain,(
% 3.68/0.86    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK3(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 3.68/0.86    introduced(choice_axiom,[])).
% 3.68/0.86  
% 3.68/0.86  fof(f38,plain,(
% 3.68/0.86    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK3(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK4(X0,X1,X2,X5)) & m1_subset_1(sK4(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.68/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f37,f36])).
% 3.68/0.86  
% 3.68/0.86  fof(f57,plain,(
% 3.68/0.86    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f38])).
% 3.68/0.86  
% 3.68/0.86  fof(f67,plain,(
% 3.68/0.86    l1_waybel_0(sK6,sK5)),
% 3.68/0.86    inference(cnf_transformation,[],[f42])).
% 3.68/0.86  
% 3.68/0.86  fof(f66,plain,(
% 3.68/0.86    ~v2_struct_0(sK6)),
% 3.68/0.86    inference(cnf_transformation,[],[f42])).
% 3.68/0.86  
% 3.68/0.86  fof(f65,plain,(
% 3.68/0.86    l1_struct_0(sK5)),
% 3.68/0.86    inference(cnf_transformation,[],[f42])).
% 3.68/0.86  
% 3.68/0.86  fof(f64,plain,(
% 3.68/0.86    ~v2_struct_0(sK5)),
% 3.68/0.86    inference(cnf_transformation,[],[f42])).
% 3.68/0.86  
% 3.68/0.86  cnf(c_4,plain,
% 3.68/0.86      ( r2_hidden(sK1(X0,X1,X2),X0)
% 3.68/0.86      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.68/0.86      | k6_subset_1(X0,X1) = X2 ),
% 3.68/0.86      inference(cnf_transformation,[],[f71]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_1204,plain,
% 3.68/0.86      ( k6_subset_1(X0,X1) = X2
% 3.68/0.86      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 3.68/0.86      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 3.68/0.86      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_2100,plain,
% 3.68/0.86      ( k6_subset_1(X0,X1) = X0
% 3.68/0.86      | r2_hidden(sK1(X0,X1,X0),X0) = iProver_top
% 3.68/0.86      | iProver_top != iProver_top ),
% 3.68/0.86      inference(equality_factoring,[status(thm)],[c_1204]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_2102,plain,
% 3.68/0.86      ( k6_subset_1(X0,X1) = X0
% 3.68/0.86      | r2_hidden(sK1(X0,X1,X0),X0) = iProver_top ),
% 3.68/0.86      inference(equality_resolution_simp,[status(thm)],[c_2100]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_2,plain,
% 3.68/0.86      ( ~ r2_hidden(sK1(X0,X1,X2),X0)
% 3.68/0.86      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 3.68/0.86      | r2_hidden(sK1(X0,X1,X2),X1)
% 3.68/0.86      | k6_subset_1(X0,X1) = X2 ),
% 3.68/0.86      inference(cnf_transformation,[],[f69]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_1206,plain,
% 3.68/0.86      ( k6_subset_1(X0,X1) = X2
% 3.68/0.86      | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top
% 3.68/0.86      | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
% 3.68/0.86      | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
% 3.68/0.86      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_2406,plain,
% 3.68/0.86      ( k6_subset_1(X0,X1) = X0
% 3.68/0.86      | r2_hidden(sK1(X0,X1,X0),X0) != iProver_top
% 3.68/0.86      | r2_hidden(sK1(X0,X1,X0),X1) = iProver_top ),
% 3.68/0.86      inference(superposition,[status(thm)],[c_2102,c_1206]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_2424,plain,
% 3.68/0.86      ( k6_subset_1(X0,X1) = X0
% 3.68/0.86      | r2_hidden(sK1(X0,X1,X0),X1) = iProver_top ),
% 3.68/0.86      inference(forward_subsumption_resolution,
% 3.68/0.86                [status(thm)],
% 3.68/0.86                [c_2406,c_2102]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_9,plain,
% 3.68/0.86      ( m1_subset_1(sK2(X0),X0) ),
% 3.68/0.86      inference(cnf_transformation,[],[f52]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_1200,plain,
% 3.68/0.86      ( m1_subset_1(sK2(X0),X0) = iProver_top ),
% 3.68/0.86      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_8,plain,
% 3.68/0.86      ( v1_xboole_0(k1_xboole_0) ),
% 3.68/0.86      inference(cnf_transformation,[],[f51]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_10,plain,
% 3.68/0.86      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.68/0.86      | ~ r2_hidden(X2,X0)
% 3.68/0.86      | ~ v1_xboole_0(X1) ),
% 3.68/0.86      inference(cnf_transformation,[],[f54]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_271,plain,
% 3.68/0.86      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.68/0.86      | ~ r2_hidden(X2,X0)
% 3.68/0.86      | k1_xboole_0 != X1 ),
% 3.68/0.86      inference(resolution_lifted,[status(thm)],[c_8,c_10]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_272,plain,
% 3.68/0.86      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~ r2_hidden(X1,X0) ),
% 3.68/0.86      inference(unflattening,[status(thm)],[c_271]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_1187,plain,
% 3.68/0.86      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/0.86      | r2_hidden(X1,X0) != iProver_top ),
% 3.68/0.86      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_1498,plain,
% 3.68/0.86      ( r2_hidden(X0,sK2(k1_zfmisc_1(k1_xboole_0))) != iProver_top ),
% 3.68/0.86      inference(superposition,[status(thm)],[c_1200,c_1187]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_2767,plain,
% 3.68/0.86      ( k6_subset_1(X0,sK2(k1_zfmisc_1(k1_xboole_0))) = X0 ),
% 3.68/0.86      inference(superposition,[status(thm)],[c_2424,c_1498]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_16,plain,
% 3.68/0.86      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 3.68/0.86      | r2_waybel_0(X0,X1,X2)
% 3.68/0.86      | ~ l1_waybel_0(X1,X0)
% 3.68/0.86      | ~ l1_struct_0(X0)
% 3.68/0.86      | v2_struct_0(X0)
% 3.68/0.86      | v2_struct_0(X1) ),
% 3.68/0.86      inference(cnf_transformation,[],[f61]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_1196,plain,
% 3.68/0.86      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) = iProver_top
% 3.68/0.86      | r2_waybel_0(X0,X1,X2) = iProver_top
% 3.68/0.86      | l1_waybel_0(X1,X0) != iProver_top
% 3.68/0.86      | l1_struct_0(X0) != iProver_top
% 3.68/0.86      | v2_struct_0(X0) = iProver_top
% 3.68/0.86      | v2_struct_0(X1) = iProver_top ),
% 3.68/0.86      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_2892,plain,
% 3.68/0.86      ( r1_waybel_0(X0,X1,u1_struct_0(X0)) = iProver_top
% 3.68/0.86      | r2_waybel_0(X0,X1,sK2(k1_zfmisc_1(k1_xboole_0))) = iProver_top
% 3.68/0.86      | l1_waybel_0(X1,X0) != iProver_top
% 3.68/0.86      | l1_struct_0(X0) != iProver_top
% 3.68/0.86      | v2_struct_0(X0) = iProver_top
% 3.68/0.86      | v2_struct_0(X1) = iProver_top ),
% 3.68/0.86      inference(superposition,[status(thm)],[c_2767,c_1196]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_20,negated_conjecture,
% 3.68/0.86      ( ~ r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) ),
% 3.68/0.86      inference(cnf_transformation,[],[f68]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_1192,plain,
% 3.68/0.86      ( r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) != iProver_top ),
% 3.68/0.86      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_14578,plain,
% 3.68/0.86      ( r2_waybel_0(sK5,sK6,sK2(k1_zfmisc_1(k1_xboole_0))) = iProver_top
% 3.68/0.86      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.68/0.86      | l1_struct_0(sK5) != iProver_top
% 3.68/0.86      | v2_struct_0(sK6) = iProver_top
% 3.68/0.86      | v2_struct_0(sK5) = iProver_top ),
% 3.68/0.86      inference(superposition,[status(thm)],[c_2892,c_1192]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_1478,plain,
% 3.68/0.86      ( ~ m1_subset_1(sK2(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
% 3.68/0.86      | ~ r2_hidden(X0,sK2(k1_zfmisc_1(k1_xboole_0))) ),
% 3.68/0.86      inference(instantiation,[status(thm)],[c_272]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_2986,plain,
% 3.68/0.86      ( ~ m1_subset_1(sK2(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
% 3.68/0.86      | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,sK2(k1_zfmisc_1(k1_xboole_0)),sK2(u1_struct_0(sK6)))),sK2(k1_zfmisc_1(k1_xboole_0))) ),
% 3.68/0.86      inference(instantiation,[status(thm)],[c_1478]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_2989,plain,
% 3.68/0.86      ( m1_subset_1(sK2(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/0.86      | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,sK2(k1_zfmisc_1(k1_xboole_0)),sK2(u1_struct_0(sK6)))),sK2(k1_zfmisc_1(k1_xboole_0))) != iProver_top ),
% 3.68/0.86      inference(predicate_to_equality,[status(thm)],[c_2986]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_13,plain,
% 3.68/0.86      ( ~ r2_waybel_0(X0,X1,X2)
% 3.68/0.86      | ~ l1_waybel_0(X1,X0)
% 3.68/0.86      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.68/0.86      | r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2)
% 3.68/0.86      | ~ l1_struct_0(X0)
% 3.68/0.86      | v2_struct_0(X0)
% 3.68/0.86      | v2_struct_0(X1) ),
% 3.68/0.86      inference(cnf_transformation,[],[f57]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_1466,plain,
% 3.68/0.86      ( ~ r2_waybel_0(sK5,sK6,X0)
% 3.68/0.86      | ~ l1_waybel_0(sK6,sK5)
% 3.68/0.86      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.68/0.86      | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,X1)),X0)
% 3.68/0.86      | ~ l1_struct_0(sK5)
% 3.68/0.86      | v2_struct_0(sK6)
% 3.68/0.86      | v2_struct_0(sK5) ),
% 3.68/0.86      inference(instantiation,[status(thm)],[c_13]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_1585,plain,
% 3.68/0.86      ( ~ r2_waybel_0(sK5,sK6,X0)
% 3.68/0.86      | ~ l1_waybel_0(sK6,sK5)
% 3.68/0.86      | ~ m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6))
% 3.68/0.86      | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,sK2(u1_struct_0(sK6)))),X0)
% 3.68/0.86      | ~ l1_struct_0(sK5)
% 3.68/0.86      | v2_struct_0(sK6)
% 3.68/0.86      | v2_struct_0(sK5) ),
% 3.68/0.86      inference(instantiation,[status(thm)],[c_1466]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_2985,plain,
% 3.68/0.86      ( ~ r2_waybel_0(sK5,sK6,sK2(k1_zfmisc_1(k1_xboole_0)))
% 3.68/0.86      | ~ l1_waybel_0(sK6,sK5)
% 3.68/0.86      | ~ m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6))
% 3.68/0.86      | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,sK2(k1_zfmisc_1(k1_xboole_0)),sK2(u1_struct_0(sK6)))),sK2(k1_zfmisc_1(k1_xboole_0)))
% 3.68/0.86      | ~ l1_struct_0(sK5)
% 3.68/0.86      | v2_struct_0(sK6)
% 3.68/0.86      | v2_struct_0(sK5) ),
% 3.68/0.86      inference(instantiation,[status(thm)],[c_1585]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_2987,plain,
% 3.68/0.86      ( r2_waybel_0(sK5,sK6,sK2(k1_zfmisc_1(k1_xboole_0))) != iProver_top
% 3.68/0.86      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.68/0.86      | m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
% 3.68/0.86      | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,sK2(k1_zfmisc_1(k1_xboole_0)),sK2(u1_struct_0(sK6)))),sK2(k1_zfmisc_1(k1_xboole_0))) = iProver_top
% 3.68/0.86      | l1_struct_0(sK5) != iProver_top
% 3.68/0.86      | v2_struct_0(sK6) = iProver_top
% 3.68/0.86      | v2_struct_0(sK5) = iProver_top ),
% 3.68/0.86      inference(predicate_to_equality,[status(thm)],[c_2985]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_1529,plain,
% 3.68/0.86      ( m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6)) ),
% 3.68/0.86      inference(instantiation,[status(thm)],[c_9]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_1534,plain,
% 3.68/0.86      ( m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
% 3.68/0.86      inference(predicate_to_equality,[status(thm)],[c_1529]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_1479,plain,
% 3.68/0.86      ( m1_subset_1(sK2(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
% 3.68/0.86      inference(instantiation,[status(thm)],[c_9]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_1484,plain,
% 3.68/0.86      ( m1_subset_1(sK2(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.68/0.86      inference(predicate_to_equality,[status(thm)],[c_1479]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_21,negated_conjecture,
% 3.68/0.86      ( l1_waybel_0(sK6,sK5) ),
% 3.68/0.86      inference(cnf_transformation,[],[f67]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_28,plain,
% 3.68/0.86      ( l1_waybel_0(sK6,sK5) = iProver_top ),
% 3.68/0.86      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_22,negated_conjecture,
% 3.68/0.86      ( ~ v2_struct_0(sK6) ),
% 3.68/0.86      inference(cnf_transformation,[],[f66]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_27,plain,
% 3.68/0.86      ( v2_struct_0(sK6) != iProver_top ),
% 3.68/0.86      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_23,negated_conjecture,
% 3.68/0.86      ( l1_struct_0(sK5) ),
% 3.68/0.86      inference(cnf_transformation,[],[f65]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_26,plain,
% 3.68/0.86      ( l1_struct_0(sK5) = iProver_top ),
% 3.68/0.86      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_24,negated_conjecture,
% 3.68/0.86      ( ~ v2_struct_0(sK5) ),
% 3.68/0.86      inference(cnf_transformation,[],[f64]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(c_25,plain,
% 3.68/0.86      ( v2_struct_0(sK5) != iProver_top ),
% 3.68/0.86      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.68/0.86  
% 3.68/0.86  cnf(contradiction,plain,
% 3.68/0.86      ( $false ),
% 3.68/0.86      inference(minisat,
% 3.68/0.86                [status(thm)],
% 3.68/0.86                [c_14578,c_2989,c_2987,c_1534,c_1484,c_28,c_27,c_26,c_25]) ).
% 3.68/0.86  
% 3.68/0.86  
% 3.68/0.86  % SZS output end CNFRefutation for theBenchmark.p
% 3.68/0.86  
% 3.68/0.86  ------                               Statistics
% 3.68/0.86  
% 3.68/0.86  ------ General
% 3.68/0.86  
% 3.68/0.86  abstr_ref_over_cycles:                  0
% 3.68/0.86  abstr_ref_under_cycles:                 0
% 3.68/0.86  gc_basic_clause_elim:                   0
% 3.68/0.86  forced_gc_time:                         0
% 3.68/0.86  parsing_time:                           0.007
% 3.68/0.86  unif_index_cands_time:                  0.
% 3.68/0.86  unif_index_add_time:                    0.
% 3.68/0.86  orderings_time:                         0.
% 3.68/0.86  out_proof_time:                         0.008
% 3.68/0.86  total_time:                             0.372
% 3.68/0.86  num_of_symbols:                         53
% 3.68/0.86  num_of_terms:                           15513
% 3.68/0.86  
% 3.68/0.86  ------ Preprocessing
% 3.68/0.86  
% 3.68/0.86  num_of_splits:                          0
% 3.68/0.86  num_of_split_atoms:                     0
% 3.68/0.86  num_of_reused_defs:                     0
% 3.68/0.86  num_eq_ax_congr_red:                    63
% 3.68/0.86  num_of_sem_filtered_clauses:            1
% 3.68/0.86  num_of_subtypes:                        0
% 3.68/0.86  monotx_restored_types:                  0
% 3.68/0.86  sat_num_of_epr_types:                   0
% 3.68/0.86  sat_num_of_non_cyclic_types:            0
% 3.68/0.86  sat_guarded_non_collapsed_types:        0
% 3.68/0.86  num_pure_diseq_elim:                    0
% 3.68/0.86  simp_replaced_by:                       0
% 3.68/0.86  res_preprocessed:                       121
% 3.68/0.86  prep_upred:                             0
% 3.68/0.86  prep_unflattend:                        20
% 3.68/0.86  smt_new_axioms:                         0
% 3.68/0.86  pred_elim_cands:                        8
% 3.68/0.86  pred_elim:                              2
% 3.68/0.86  pred_elim_cl:                           2
% 3.68/0.86  pred_elim_cycles:                       4
% 3.68/0.86  merged_defs:                            0
% 3.68/0.86  merged_defs_ncl:                        0
% 3.68/0.86  bin_hyper_res:                          0
% 3.68/0.86  prep_cycles:                            4
% 3.68/0.86  pred_elim_time:                         0.006
% 3.68/0.86  splitting_time:                         0.
% 3.68/0.86  sem_filter_time:                        0.
% 3.68/0.86  monotx_time:                            0.001
% 3.68/0.86  subtype_inf_time:                       0.
% 3.68/0.86  
% 3.68/0.86  ------ Problem properties
% 3.68/0.86  
% 3.68/0.86  clauses:                                23
% 3.68/0.86  conjectures:                            5
% 3.68/0.86  epr:                                    6
% 3.68/0.86  horn:                                   10
% 3.68/0.86  ground:                                 5
% 3.68/0.86  unary:                                  6
% 3.68/0.86  binary:                                 5
% 3.68/0.86  lits:                                   85
% 3.68/0.86  lits_eq:                                3
% 3.68/0.86  fd_pure:                                0
% 3.68/0.86  fd_pseudo:                              0
% 3.68/0.86  fd_cond:                                0
% 3.68/0.86  fd_pseudo_cond:                         3
% 3.68/0.86  ac_symbols:                             0
% 3.68/0.86  
% 3.68/0.86  ------ Propositional Solver
% 3.68/0.86  
% 3.68/0.86  prop_solver_calls:                      29
% 3.68/0.86  prop_fast_solver_calls:                 1110
% 3.68/0.86  smt_solver_calls:                       0
% 3.68/0.86  smt_fast_solver_calls:                  0
% 3.68/0.86  prop_num_of_clauses:                    3116
% 3.68/0.86  prop_preprocess_simplified:             8595
% 3.68/0.86  prop_fo_subsumed:                       0
% 3.68/0.86  prop_solver_time:                       0.
% 3.68/0.86  smt_solver_time:                        0.
% 3.68/0.86  smt_fast_solver_time:                   0.
% 3.68/0.86  prop_fast_solver_time:                  0.
% 3.68/0.86  prop_unsat_core_time:                   0.
% 3.68/0.86  
% 3.68/0.86  ------ QBF
% 3.68/0.86  
% 3.68/0.86  qbf_q_res:                              0
% 3.68/0.86  qbf_num_tautologies:                    0
% 3.68/0.86  qbf_prep_cycles:                        0
% 3.68/0.86  
% 3.68/0.86  ------ BMC1
% 3.68/0.86  
% 3.68/0.86  bmc1_current_bound:                     -1
% 3.68/0.86  bmc1_last_solved_bound:                 -1
% 3.68/0.86  bmc1_unsat_core_size:                   -1
% 3.68/0.86  bmc1_unsat_core_parents_size:           -1
% 3.68/0.86  bmc1_merge_next_fun:                    0
% 3.68/0.86  bmc1_unsat_core_clauses_time:           0.
% 3.68/0.86  
% 3.68/0.86  ------ Instantiation
% 3.68/0.86  
% 3.68/0.86  inst_num_of_clauses:                    727
% 3.68/0.86  inst_num_in_passive:                    355
% 3.68/0.86  inst_num_in_active:                     285
% 3.68/0.86  inst_num_in_unprocessed:                87
% 3.68/0.86  inst_num_of_loops:                      430
% 3.68/0.86  inst_num_of_learning_restarts:          0
% 3.68/0.86  inst_num_moves_active_passive:          141
% 3.68/0.86  inst_lit_activity:                      0
% 3.68/0.86  inst_lit_activity_moves:                0
% 3.68/0.86  inst_num_tautologies:                   0
% 3.68/0.86  inst_num_prop_implied:                  0
% 3.68/0.86  inst_num_existing_simplified:           0
% 3.68/0.86  inst_num_eq_res_simplified:             0
% 3.68/0.86  inst_num_child_elim:                    0
% 3.68/0.86  inst_num_of_dismatching_blockings:      302
% 3.68/0.86  inst_num_of_non_proper_insts:           560
% 3.68/0.86  inst_num_of_duplicates:                 0
% 3.68/0.86  inst_inst_num_from_inst_to_res:         0
% 3.68/0.86  inst_dismatching_checking_time:         0.
% 3.68/0.86  
% 3.68/0.86  ------ Resolution
% 3.68/0.86  
% 3.68/0.86  res_num_of_clauses:                     0
% 3.68/0.86  res_num_in_passive:                     0
% 3.68/0.86  res_num_in_active:                      0
% 3.68/0.86  res_num_of_loops:                       125
% 3.68/0.86  res_forward_subset_subsumed:            41
% 3.68/0.86  res_backward_subset_subsumed:           0
% 3.68/0.86  res_forward_subsumed:                   0
% 3.68/0.86  res_backward_subsumed:                  0
% 3.68/0.86  res_forward_subsumption_resolution:     2
% 3.68/0.86  res_backward_subsumption_resolution:    0
% 3.68/0.86  res_clause_to_clause_subsumption:       7419
% 3.68/0.86  res_orphan_elimination:                 0
% 3.68/0.86  res_tautology_del:                      84
% 3.68/0.86  res_num_eq_res_simplified:              0
% 3.68/0.86  res_num_sel_changes:                    0
% 3.68/0.86  res_moves_from_active_to_pass:          0
% 3.68/0.86  
% 3.68/0.86  ------ Superposition
% 3.68/0.86  
% 3.68/0.86  sup_time_total:                         0.
% 3.68/0.86  sup_time_generating:                    0.
% 3.68/0.86  sup_time_sim_full:                      0.
% 3.68/0.86  sup_time_sim_immed:                     0.
% 3.68/0.86  
% 3.68/0.86  sup_num_of_clauses:                     383
% 3.68/0.86  sup_num_in_active:                      83
% 3.68/0.86  sup_num_in_passive:                     300
% 3.68/0.86  sup_num_of_loops:                       85
% 3.68/0.86  sup_fw_superposition:                   2013
% 3.68/0.86  sup_bw_superposition:                   1744
% 3.68/0.86  sup_immediate_simplified:               1485
% 3.68/0.86  sup_given_eliminated:                   1
% 3.68/0.86  comparisons_done:                       0
% 3.68/0.86  comparisons_avoided:                    0
% 3.68/0.86  
% 3.68/0.86  ------ Simplifications
% 3.68/0.86  
% 3.68/0.86  
% 3.68/0.86  sim_fw_subset_subsumed:                 35
% 3.68/0.86  sim_bw_subset_subsumed:                 0
% 3.68/0.86  sim_fw_subsumed:                        452
% 3.68/0.86  sim_bw_subsumed:                        1
% 3.68/0.86  sim_fw_subsumption_res:                 2
% 3.68/0.86  sim_bw_subsumption_res:                 0
% 3.68/0.86  sim_tautology_del:                      56
% 3.68/0.86  sim_eq_tautology_del:                   195
% 3.68/0.86  sim_eq_res_simp:                        1
% 3.68/0.86  sim_fw_demodulated:                     575
% 3.68/0.86  sim_bw_demodulated:                     3
% 3.68/0.86  sim_light_normalised:                   531
% 3.68/0.86  sim_joinable_taut:                      0
% 3.68/0.86  sim_joinable_simp:                      0
% 3.68/0.86  sim_ac_normalised:                      0
% 3.68/0.86  sim_smt_subsumption:                    0
% 3.68/0.86  
%------------------------------------------------------------------------------
