%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:15 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 107 expanded)
%              Number of clauses        :   27 (  27 expanded)
%              Number of leaves         :   14 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :  287 ( 511 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

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
     => ( r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK2(X0,X1,X2,X5))
        & m1_subset_1(sK2(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
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
            | ~ r1_orders_2(X1,sK1(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f34,f33])).

fof(f50,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f41,f43])).

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
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_waybel_0(X0,sK4,u1_struct_0(X0))
        & l1_waybel_0(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
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
          ( ~ r1_waybel_0(sK3,X1,u1_struct_0(sK3))
          & l1_waybel_0(X1,sK3)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3))
    & l1_waybel_0(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f38,f37])).

fof(f61,plain,(
    ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3,f29])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f60,plain,(
    l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_221,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_222,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_1308,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_1697,plain,
    ( ~ r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k1_xboole_0,sK0(u1_struct_0(sK4)))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_9,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1288,plain,
    ( ~ r2_waybel_0(sK3,sK4,X0)
    | ~ l1_waybel_0(sK4,sK3)
    | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1418,plain,
    ( ~ r2_waybel_0(sK3,sK4,X0)
    | ~ l1_waybel_0(sK4,sK3)
    | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,X0,sK0(u1_struct_0(sK4)))),X0)
    | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1288])).

cnf(c_1696,plain,
    ( ~ r2_waybel_0(sK3,sK4,k1_xboole_0)
    | ~ l1_waybel_0(sK4,sK3)
    | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k1_xboole_0,sK0(u1_struct_0(sK4)))),k1_xboole_0)
    | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1418])).

cnf(c_1,plain,
    ( k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_12,plain,
    ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1068,plain,
    ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) = iProver_top
    | r2_waybel_0(X0,X1,X2) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1523,plain,
    ( r1_waybel_0(X0,X1,u1_struct_0(X0)) = iProver_top
    | r2_waybel_0(X0,X1,k1_xboole_0) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1068])).

cnf(c_16,negated_conjecture,
    ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1066,plain,
    ( r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1534,plain,
    ( r2_waybel_0(sK3,sK4,k1_xboole_0) = iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1523,c_1066])).

cnf(c_1535,plain,
    ( r2_waybel_0(sK3,sK4,k1_xboole_0)
    | ~ l1_waybel_0(sK4,sK3)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1534])).

cnf(c_2,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1342,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1309,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_17,negated_conjecture,
    ( l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1697,c_1696,c_1535,c_1342,c_1309,c_17,c_18,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:19:14 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 1.51/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/0.98  
% 1.51/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.51/0.98  
% 1.51/0.98  ------  iProver source info
% 1.51/0.98  
% 1.51/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.51/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.51/0.98  git: non_committed_changes: false
% 1.51/0.98  git: last_make_outside_of_git: false
% 1.51/0.98  
% 1.51/0.98  ------ 
% 1.51/0.98  
% 1.51/0.98  ------ Input Options
% 1.51/0.98  
% 1.51/0.98  --out_options                           all
% 1.51/0.98  --tptp_safe_out                         true
% 1.51/0.98  --problem_path                          ""
% 1.51/0.98  --include_path                          ""
% 1.51/0.98  --clausifier                            res/vclausify_rel
% 1.51/0.98  --clausifier_options                    --mode clausify
% 1.51/0.98  --stdin                                 false
% 1.51/0.98  --stats_out                             all
% 1.51/0.98  
% 1.51/0.98  ------ General Options
% 1.51/0.98  
% 1.51/0.98  --fof                                   false
% 1.51/0.98  --time_out_real                         305.
% 1.51/0.98  --time_out_virtual                      -1.
% 1.51/0.98  --symbol_type_check                     false
% 1.51/0.98  --clausify_out                          false
% 1.51/0.98  --sig_cnt_out                           false
% 1.51/0.98  --trig_cnt_out                          false
% 1.51/0.98  --trig_cnt_out_tolerance                1.
% 1.51/0.98  --trig_cnt_out_sk_spl                   false
% 1.51/0.98  --abstr_cl_out                          false
% 1.51/0.98  
% 1.51/0.98  ------ Global Options
% 1.51/0.98  
% 1.51/0.98  --schedule                              default
% 1.51/0.98  --add_important_lit                     false
% 1.51/0.98  --prop_solver_per_cl                    1000
% 1.51/0.98  --min_unsat_core                        false
% 1.51/0.98  --soft_assumptions                      false
% 1.51/0.98  --soft_lemma_size                       3
% 1.51/0.98  --prop_impl_unit_size                   0
% 1.51/0.98  --prop_impl_unit                        []
% 1.51/0.98  --share_sel_clauses                     true
% 1.51/0.98  --reset_solvers                         false
% 1.51/0.98  --bc_imp_inh                            [conj_cone]
% 1.51/0.98  --conj_cone_tolerance                   3.
% 1.51/0.98  --extra_neg_conj                        none
% 1.51/0.98  --large_theory_mode                     true
% 1.51/0.98  --prolific_symb_bound                   200
% 1.51/0.98  --lt_threshold                          2000
% 1.51/0.98  --clause_weak_htbl                      true
% 1.51/0.98  --gc_record_bc_elim                     false
% 1.51/0.98  
% 1.51/0.98  ------ Preprocessing Options
% 1.51/0.98  
% 1.51/0.98  --preprocessing_flag                    true
% 1.51/0.98  --time_out_prep_mult                    0.1
% 1.51/0.98  --splitting_mode                        input
% 1.51/0.98  --splitting_grd                         true
% 1.51/0.98  --splitting_cvd                         false
% 1.51/0.98  --splitting_cvd_svl                     false
% 1.51/0.98  --splitting_nvd                         32
% 1.51/0.98  --sub_typing                            true
% 1.51/0.98  --prep_gs_sim                           true
% 1.51/0.98  --prep_unflatten                        true
% 1.51/0.98  --prep_res_sim                          true
% 1.51/0.98  --prep_upred                            true
% 1.51/0.98  --prep_sem_filter                       exhaustive
% 1.51/0.98  --prep_sem_filter_out                   false
% 1.51/0.98  --pred_elim                             true
% 1.51/0.98  --res_sim_input                         true
% 1.51/0.98  --eq_ax_congr_red                       true
% 1.51/0.98  --pure_diseq_elim                       true
% 1.51/0.98  --brand_transform                       false
% 1.51/0.98  --non_eq_to_eq                          false
% 1.51/0.98  --prep_def_merge                        true
% 1.51/0.98  --prep_def_merge_prop_impl              false
% 1.51/0.98  --prep_def_merge_mbd                    true
% 1.51/0.98  --prep_def_merge_tr_red                 false
% 1.51/0.98  --prep_def_merge_tr_cl                  false
% 1.51/0.98  --smt_preprocessing                     true
% 1.51/0.98  --smt_ac_axioms                         fast
% 1.51/0.98  --preprocessed_out                      false
% 1.51/0.98  --preprocessed_stats                    false
% 1.51/0.98  
% 1.51/0.98  ------ Abstraction refinement Options
% 1.51/0.98  
% 1.51/0.98  --abstr_ref                             []
% 1.51/0.98  --abstr_ref_prep                        false
% 1.51/0.98  --abstr_ref_until_sat                   false
% 1.51/0.98  --abstr_ref_sig_restrict                funpre
% 1.51/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.51/0.98  --abstr_ref_under                       []
% 1.51/0.98  
% 1.51/0.98  ------ SAT Options
% 1.51/0.98  
% 1.51/0.98  --sat_mode                              false
% 1.51/0.98  --sat_fm_restart_options                ""
% 1.51/0.98  --sat_gr_def                            false
% 1.51/0.98  --sat_epr_types                         true
% 1.51/0.98  --sat_non_cyclic_types                  false
% 1.51/0.98  --sat_finite_models                     false
% 1.51/0.98  --sat_fm_lemmas                         false
% 1.51/0.98  --sat_fm_prep                           false
% 1.51/0.98  --sat_fm_uc_incr                        true
% 1.51/0.98  --sat_out_model                         small
% 1.51/0.98  --sat_out_clauses                       false
% 1.51/0.98  
% 1.51/0.98  ------ QBF Options
% 1.51/0.98  
% 1.51/0.98  --qbf_mode                              false
% 1.51/0.98  --qbf_elim_univ                         false
% 1.51/0.98  --qbf_dom_inst                          none
% 1.51/0.98  --qbf_dom_pre_inst                      false
% 1.51/0.98  --qbf_sk_in                             false
% 1.51/0.98  --qbf_pred_elim                         true
% 1.51/0.98  --qbf_split                             512
% 1.51/0.98  
% 1.51/0.98  ------ BMC1 Options
% 1.51/0.98  
% 1.51/0.98  --bmc1_incremental                      false
% 1.51/0.98  --bmc1_axioms                           reachable_all
% 1.51/0.98  --bmc1_min_bound                        0
% 1.51/0.98  --bmc1_max_bound                        -1
% 1.51/0.98  --bmc1_max_bound_default                -1
% 1.51/0.98  --bmc1_symbol_reachability              true
% 1.51/0.98  --bmc1_property_lemmas                  false
% 1.51/0.98  --bmc1_k_induction                      false
% 1.51/0.98  --bmc1_non_equiv_states                 false
% 1.51/0.98  --bmc1_deadlock                         false
% 1.51/0.98  --bmc1_ucm                              false
% 1.51/0.98  --bmc1_add_unsat_core                   none
% 1.51/0.98  --bmc1_unsat_core_children              false
% 1.51/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.51/0.98  --bmc1_out_stat                         full
% 1.51/0.98  --bmc1_ground_init                      false
% 1.51/0.98  --bmc1_pre_inst_next_state              false
% 1.51/0.98  --bmc1_pre_inst_state                   false
% 1.51/0.98  --bmc1_pre_inst_reach_state             false
% 1.51/0.98  --bmc1_out_unsat_core                   false
% 1.51/0.98  --bmc1_aig_witness_out                  false
% 1.51/0.98  --bmc1_verbose                          false
% 1.51/0.98  --bmc1_dump_clauses_tptp                false
% 1.51/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.51/0.98  --bmc1_dump_file                        -
% 1.51/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.51/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.51/0.98  --bmc1_ucm_extend_mode                  1
% 1.51/0.98  --bmc1_ucm_init_mode                    2
% 1.51/0.98  --bmc1_ucm_cone_mode                    none
% 1.51/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.51/0.98  --bmc1_ucm_relax_model                  4
% 1.51/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.51/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.51/0.98  --bmc1_ucm_layered_model                none
% 1.51/0.98  --bmc1_ucm_max_lemma_size               10
% 1.51/0.98  
% 1.51/0.98  ------ AIG Options
% 1.51/0.98  
% 1.51/0.98  --aig_mode                              false
% 1.51/0.98  
% 1.51/0.98  ------ Instantiation Options
% 1.51/0.98  
% 1.51/0.98  --instantiation_flag                    true
% 1.51/0.98  --inst_sos_flag                         false
% 1.51/0.98  --inst_sos_phase                        true
% 1.51/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.51/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.51/0.98  --inst_lit_sel_side                     num_symb
% 1.51/0.98  --inst_solver_per_active                1400
% 1.51/0.98  --inst_solver_calls_frac                1.
% 1.51/0.98  --inst_passive_queue_type               priority_queues
% 1.51/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.51/0.98  --inst_passive_queues_freq              [25;2]
% 1.51/0.98  --inst_dismatching                      true
% 1.51/0.98  --inst_eager_unprocessed_to_passive     true
% 1.51/0.98  --inst_prop_sim_given                   true
% 1.51/0.98  --inst_prop_sim_new                     false
% 1.51/0.98  --inst_subs_new                         false
% 1.51/0.98  --inst_eq_res_simp                      false
% 1.51/0.98  --inst_subs_given                       false
% 1.51/0.98  --inst_orphan_elimination               true
% 1.51/0.98  --inst_learning_loop_flag               true
% 1.51/0.98  --inst_learning_start                   3000
% 1.51/0.98  --inst_learning_factor                  2
% 1.51/0.98  --inst_start_prop_sim_after_learn       3
% 1.51/0.98  --inst_sel_renew                        solver
% 1.51/0.98  --inst_lit_activity_flag                true
% 1.51/0.98  --inst_restr_to_given                   false
% 1.51/0.98  --inst_activity_threshold               500
% 1.51/0.98  --inst_out_proof                        true
% 1.51/0.98  
% 1.51/0.98  ------ Resolution Options
% 1.51/0.98  
% 1.51/0.98  --resolution_flag                       true
% 1.51/0.98  --res_lit_sel                           adaptive
% 1.51/0.98  --res_lit_sel_side                      none
% 1.51/0.98  --res_ordering                          kbo
% 1.51/0.98  --res_to_prop_solver                    active
% 1.51/0.98  --res_prop_simpl_new                    false
% 1.51/0.98  --res_prop_simpl_given                  true
% 1.51/0.98  --res_passive_queue_type                priority_queues
% 1.51/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.51/0.98  --res_passive_queues_freq               [15;5]
% 1.51/0.98  --res_forward_subs                      full
% 1.51/0.98  --res_backward_subs                     full
% 1.51/0.98  --res_forward_subs_resolution           true
% 1.51/0.98  --res_backward_subs_resolution          true
% 1.51/0.98  --res_orphan_elimination                true
% 1.51/0.98  --res_time_limit                        2.
% 1.51/0.98  --res_out_proof                         true
% 1.51/0.98  
% 1.51/0.98  ------ Superposition Options
% 1.51/0.98  
% 1.51/0.98  --superposition_flag                    true
% 1.51/0.98  --sup_passive_queue_type                priority_queues
% 1.51/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.51/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.51/0.98  --demod_completeness_check              fast
% 1.51/0.98  --demod_use_ground                      true
% 1.51/0.98  --sup_to_prop_solver                    passive
% 1.51/0.98  --sup_prop_simpl_new                    true
% 1.51/0.98  --sup_prop_simpl_given                  true
% 1.51/0.98  --sup_fun_splitting                     false
% 1.51/0.98  --sup_smt_interval                      50000
% 1.51/0.98  
% 1.51/0.98  ------ Superposition Simplification Setup
% 1.51/0.98  
% 1.51/0.98  --sup_indices_passive                   []
% 1.51/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.51/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.98  --sup_full_bw                           [BwDemod]
% 1.51/0.98  --sup_immed_triv                        [TrivRules]
% 1.51/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.51/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.98  --sup_immed_bw_main                     []
% 1.51/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.51/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/0.98  
% 1.51/0.98  ------ Combination Options
% 1.51/0.98  
% 1.51/0.98  --comb_res_mult                         3
% 1.51/0.98  --comb_sup_mult                         2
% 1.51/0.98  --comb_inst_mult                        10
% 1.51/0.98  
% 1.51/0.98  ------ Debug Options
% 1.51/0.98  
% 1.51/0.98  --dbg_backtrace                         false
% 1.51/0.98  --dbg_dump_prop_clauses                 false
% 1.51/0.98  --dbg_dump_prop_clauses_file            -
% 1.51/0.98  --dbg_out_stat                          false
% 1.51/0.98  ------ Parsing...
% 1.51/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.51/0.98  
% 1.51/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.51/0.98  
% 1.51/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.51/0.98  
% 1.51/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.51/0.98  ------ Proving...
% 1.51/0.98  ------ Problem Properties 
% 1.51/0.98  
% 1.51/0.98  
% 1.51/0.98  clauses                                 18
% 1.51/0.98  conjectures                             5
% 1.51/0.98  EPR                                     4
% 1.51/0.98  Horn                                    10
% 1.51/0.98  unary                                   8
% 1.51/0.98  binary                                  1
% 1.51/0.98  lits                                    69
% 1.51/0.98  lits eq                                 1
% 1.51/0.98  fd_pure                                 0
% 1.51/0.98  fd_pseudo                               0
% 1.51/0.98  fd_cond                                 0
% 1.51/0.98  fd_pseudo_cond                          0
% 1.51/0.98  AC symbols                              0
% 1.51/0.98  
% 1.51/0.98  ------ Schedule dynamic 5 is on 
% 1.51/0.98  
% 1.51/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.51/0.98  
% 1.51/0.98  
% 1.51/0.98  ------ 
% 1.51/0.98  Current options:
% 1.51/0.98  ------ 
% 1.51/0.98  
% 1.51/0.98  ------ Input Options
% 1.51/0.98  
% 1.51/0.98  --out_options                           all
% 1.51/0.98  --tptp_safe_out                         true
% 1.51/0.98  --problem_path                          ""
% 1.51/0.98  --include_path                          ""
% 1.51/0.98  --clausifier                            res/vclausify_rel
% 1.51/0.98  --clausifier_options                    --mode clausify
% 1.51/0.98  --stdin                                 false
% 1.51/0.98  --stats_out                             all
% 1.51/0.98  
% 1.51/0.98  ------ General Options
% 1.51/0.98  
% 1.51/0.98  --fof                                   false
% 1.51/0.98  --time_out_real                         305.
% 1.51/0.98  --time_out_virtual                      -1.
% 1.51/0.98  --symbol_type_check                     false
% 1.51/0.98  --clausify_out                          false
% 1.51/0.98  --sig_cnt_out                           false
% 1.51/0.98  --trig_cnt_out                          false
% 1.51/0.98  --trig_cnt_out_tolerance                1.
% 1.51/0.98  --trig_cnt_out_sk_spl                   false
% 1.51/0.98  --abstr_cl_out                          false
% 1.51/0.98  
% 1.51/0.98  ------ Global Options
% 1.51/0.98  
% 1.51/0.98  --schedule                              default
% 1.51/0.98  --add_important_lit                     false
% 1.51/0.98  --prop_solver_per_cl                    1000
% 1.51/0.98  --min_unsat_core                        false
% 1.51/0.98  --soft_assumptions                      false
% 1.51/0.98  --soft_lemma_size                       3
% 1.51/0.98  --prop_impl_unit_size                   0
% 1.51/0.98  --prop_impl_unit                        []
% 1.51/0.98  --share_sel_clauses                     true
% 1.51/0.98  --reset_solvers                         false
% 1.51/0.98  --bc_imp_inh                            [conj_cone]
% 1.51/0.98  --conj_cone_tolerance                   3.
% 1.51/0.98  --extra_neg_conj                        none
% 1.51/0.98  --large_theory_mode                     true
% 1.51/0.98  --prolific_symb_bound                   200
% 1.51/0.98  --lt_threshold                          2000
% 1.51/0.98  --clause_weak_htbl                      true
% 1.51/0.98  --gc_record_bc_elim                     false
% 1.51/0.98  
% 1.51/0.98  ------ Preprocessing Options
% 1.51/0.98  
% 1.51/0.98  --preprocessing_flag                    true
% 1.51/0.98  --time_out_prep_mult                    0.1
% 1.51/0.98  --splitting_mode                        input
% 1.51/0.98  --splitting_grd                         true
% 1.51/0.98  --splitting_cvd                         false
% 1.51/0.98  --splitting_cvd_svl                     false
% 1.51/0.98  --splitting_nvd                         32
% 1.51/0.98  --sub_typing                            true
% 1.51/0.98  --prep_gs_sim                           true
% 1.51/0.98  --prep_unflatten                        true
% 1.51/0.98  --prep_res_sim                          true
% 1.51/0.98  --prep_upred                            true
% 1.51/0.98  --prep_sem_filter                       exhaustive
% 1.51/0.98  --prep_sem_filter_out                   false
% 1.51/0.98  --pred_elim                             true
% 1.51/0.98  --res_sim_input                         true
% 1.51/0.98  --eq_ax_congr_red                       true
% 1.51/0.98  --pure_diseq_elim                       true
% 1.51/0.98  --brand_transform                       false
% 1.51/0.98  --non_eq_to_eq                          false
% 1.51/0.98  --prep_def_merge                        true
% 1.51/0.98  --prep_def_merge_prop_impl              false
% 1.51/0.98  --prep_def_merge_mbd                    true
% 1.51/0.98  --prep_def_merge_tr_red                 false
% 1.51/0.98  --prep_def_merge_tr_cl                  false
% 1.51/0.98  --smt_preprocessing                     true
% 1.51/0.98  --smt_ac_axioms                         fast
% 1.51/0.98  --preprocessed_out                      false
% 1.51/0.98  --preprocessed_stats                    false
% 1.51/0.98  
% 1.51/0.98  ------ Abstraction refinement Options
% 1.51/0.98  
% 1.51/0.98  --abstr_ref                             []
% 1.51/0.98  --abstr_ref_prep                        false
% 1.51/0.98  --abstr_ref_until_sat                   false
% 1.51/0.98  --abstr_ref_sig_restrict                funpre
% 1.51/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.51/0.98  --abstr_ref_under                       []
% 1.51/0.98  
% 1.51/0.98  ------ SAT Options
% 1.51/0.98  
% 1.51/0.98  --sat_mode                              false
% 1.51/0.98  --sat_fm_restart_options                ""
% 1.51/0.98  --sat_gr_def                            false
% 1.51/0.98  --sat_epr_types                         true
% 1.51/0.98  --sat_non_cyclic_types                  false
% 1.51/0.98  --sat_finite_models                     false
% 1.51/0.98  --sat_fm_lemmas                         false
% 1.51/0.98  --sat_fm_prep                           false
% 1.51/0.98  --sat_fm_uc_incr                        true
% 1.51/0.98  --sat_out_model                         small
% 1.51/0.98  --sat_out_clauses                       false
% 1.51/0.98  
% 1.51/0.98  ------ QBF Options
% 1.51/0.98  
% 1.51/0.98  --qbf_mode                              false
% 1.51/0.98  --qbf_elim_univ                         false
% 1.51/0.98  --qbf_dom_inst                          none
% 1.51/0.98  --qbf_dom_pre_inst                      false
% 1.51/0.98  --qbf_sk_in                             false
% 1.51/0.98  --qbf_pred_elim                         true
% 1.51/0.98  --qbf_split                             512
% 1.51/0.98  
% 1.51/0.98  ------ BMC1 Options
% 1.51/0.98  
% 1.51/0.98  --bmc1_incremental                      false
% 1.51/0.98  --bmc1_axioms                           reachable_all
% 1.51/0.98  --bmc1_min_bound                        0
% 1.51/0.98  --bmc1_max_bound                        -1
% 1.51/0.98  --bmc1_max_bound_default                -1
% 1.51/0.98  --bmc1_symbol_reachability              true
% 1.51/0.98  --bmc1_property_lemmas                  false
% 1.51/0.98  --bmc1_k_induction                      false
% 1.51/0.98  --bmc1_non_equiv_states                 false
% 1.51/0.98  --bmc1_deadlock                         false
% 1.51/0.98  --bmc1_ucm                              false
% 1.51/0.98  --bmc1_add_unsat_core                   none
% 1.51/0.98  --bmc1_unsat_core_children              false
% 1.51/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.51/0.98  --bmc1_out_stat                         full
% 1.51/0.98  --bmc1_ground_init                      false
% 1.51/0.98  --bmc1_pre_inst_next_state              false
% 1.51/0.98  --bmc1_pre_inst_state                   false
% 1.51/0.98  --bmc1_pre_inst_reach_state             false
% 1.51/0.98  --bmc1_out_unsat_core                   false
% 1.51/0.98  --bmc1_aig_witness_out                  false
% 1.51/0.98  --bmc1_verbose                          false
% 1.51/0.98  --bmc1_dump_clauses_tptp                false
% 1.51/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.51/0.98  --bmc1_dump_file                        -
% 1.51/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.51/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.51/0.98  --bmc1_ucm_extend_mode                  1
% 1.51/0.98  --bmc1_ucm_init_mode                    2
% 1.51/0.98  --bmc1_ucm_cone_mode                    none
% 1.51/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.51/0.98  --bmc1_ucm_relax_model                  4
% 1.51/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.51/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.51/0.98  --bmc1_ucm_layered_model                none
% 1.51/0.98  --bmc1_ucm_max_lemma_size               10
% 1.51/0.98  
% 1.51/0.98  ------ AIG Options
% 1.51/0.98  
% 1.51/0.98  --aig_mode                              false
% 1.51/0.98  
% 1.51/0.98  ------ Instantiation Options
% 1.51/0.98  
% 1.51/0.98  --instantiation_flag                    true
% 1.51/0.98  --inst_sos_flag                         false
% 1.51/0.98  --inst_sos_phase                        true
% 1.51/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.51/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.51/0.98  --inst_lit_sel_side                     none
% 1.51/0.98  --inst_solver_per_active                1400
% 1.51/0.98  --inst_solver_calls_frac                1.
% 1.51/0.98  --inst_passive_queue_type               priority_queues
% 1.51/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.51/0.98  --inst_passive_queues_freq              [25;2]
% 1.51/0.98  --inst_dismatching                      true
% 1.51/0.98  --inst_eager_unprocessed_to_passive     true
% 1.51/0.98  --inst_prop_sim_given                   true
% 1.51/0.98  --inst_prop_sim_new                     false
% 1.51/0.98  --inst_subs_new                         false
% 1.51/0.98  --inst_eq_res_simp                      false
% 1.51/0.98  --inst_subs_given                       false
% 1.51/0.98  --inst_orphan_elimination               true
% 1.51/0.98  --inst_learning_loop_flag               true
% 1.51/0.98  --inst_learning_start                   3000
% 1.51/0.98  --inst_learning_factor                  2
% 1.51/0.98  --inst_start_prop_sim_after_learn       3
% 1.51/0.98  --inst_sel_renew                        solver
% 1.51/0.98  --inst_lit_activity_flag                true
% 1.51/0.98  --inst_restr_to_given                   false
% 1.51/0.98  --inst_activity_threshold               500
% 1.51/0.98  --inst_out_proof                        true
% 1.51/0.98  
% 1.51/0.98  ------ Resolution Options
% 1.51/0.98  
% 1.51/0.98  --resolution_flag                       false
% 1.51/0.98  --res_lit_sel                           adaptive
% 1.51/0.98  --res_lit_sel_side                      none
% 1.51/0.98  --res_ordering                          kbo
% 1.51/0.98  --res_to_prop_solver                    active
% 1.51/0.98  --res_prop_simpl_new                    false
% 1.51/0.98  --res_prop_simpl_given                  true
% 1.51/0.98  --res_passive_queue_type                priority_queues
% 1.51/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.51/0.98  --res_passive_queues_freq               [15;5]
% 1.51/0.98  --res_forward_subs                      full
% 1.51/0.98  --res_backward_subs                     full
% 1.51/0.98  --res_forward_subs_resolution           true
% 1.51/0.98  --res_backward_subs_resolution          true
% 1.51/0.98  --res_orphan_elimination                true
% 1.51/0.98  --res_time_limit                        2.
% 1.51/0.98  --res_out_proof                         true
% 1.51/0.98  
% 1.51/0.98  ------ Superposition Options
% 1.51/0.98  
% 1.51/0.98  --superposition_flag                    true
% 1.51/0.98  --sup_passive_queue_type                priority_queues
% 1.51/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.51/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.51/0.98  --demod_completeness_check              fast
% 1.51/0.98  --demod_use_ground                      true
% 1.51/0.98  --sup_to_prop_solver                    passive
% 1.51/0.98  --sup_prop_simpl_new                    true
% 1.51/0.98  --sup_prop_simpl_given                  true
% 1.51/0.98  --sup_fun_splitting                     false
% 1.51/0.98  --sup_smt_interval                      50000
% 1.51/0.98  
% 1.51/0.98  ------ Superposition Simplification Setup
% 1.51/0.98  
% 1.51/0.98  --sup_indices_passive                   []
% 1.51/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.51/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.98  --sup_full_bw                           [BwDemod]
% 1.51/0.98  --sup_immed_triv                        [TrivRules]
% 1.51/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.51/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.98  --sup_immed_bw_main                     []
% 1.51/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.51/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/0.98  
% 1.51/0.98  ------ Combination Options
% 1.51/0.98  
% 1.51/0.98  --comb_res_mult                         3
% 1.51/0.98  --comb_sup_mult                         2
% 1.51/0.98  --comb_inst_mult                        10
% 1.51/0.98  
% 1.51/0.98  ------ Debug Options
% 1.51/0.98  
% 1.51/0.98  --dbg_backtrace                         false
% 1.51/0.98  --dbg_dump_prop_clauses                 false
% 1.51/0.98  --dbg_dump_prop_clauses_file            -
% 1.51/0.98  --dbg_out_stat                          false
% 1.51/0.98  
% 1.51/0.98  
% 1.51/0.98  
% 1.51/0.98  
% 1.51/0.98  ------ Proving...
% 1.51/0.98  
% 1.51/0.98  
% 1.51/0.98  % SZS status Theorem for theBenchmark.p
% 1.51/0.98  
% 1.51/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.51/0.98  
% 1.51/0.98  fof(f1,axiom,(
% 1.51/0.98    v1_xboole_0(k1_xboole_0)),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f40,plain,(
% 1.51/0.98    v1_xboole_0(k1_xboole_0)),
% 1.51/0.98    inference(cnf_transformation,[],[f1])).
% 1.51/0.98  
% 1.51/0.98  fof(f8,axiom,(
% 1.51/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f20,plain,(
% 1.51/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.51/0.98    inference(ennf_transformation,[],[f8])).
% 1.51/0.98  
% 1.51/0.98  fof(f47,plain,(
% 1.51/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.51/0.98    inference(cnf_transformation,[],[f20])).
% 1.51/0.98  
% 1.51/0.98  fof(f9,axiom,(
% 1.51/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f21,plain,(
% 1.51/0.98    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.51/0.98    inference(ennf_transformation,[],[f9])).
% 1.51/0.98  
% 1.51/0.98  fof(f22,plain,(
% 1.51/0.98    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.51/0.98    inference(flattening,[],[f21])).
% 1.51/0.98  
% 1.51/0.98  fof(f31,plain,(
% 1.51/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.51/0.98    inference(nnf_transformation,[],[f22])).
% 1.51/0.98  
% 1.51/0.98  fof(f32,plain,(
% 1.51/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.51/0.98    inference(rectify,[],[f31])).
% 1.51/0.98  
% 1.51/0.98  fof(f34,plain,(
% 1.51/0.98    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK2(X0,X1,X2,X5)) & m1_subset_1(sK2(X0,X1,X2,X5),u1_struct_0(X1))))),
% 1.51/0.98    introduced(choice_axiom,[])).
% 1.51/0.98  
% 1.51/0.98  fof(f33,plain,(
% 1.51/0.98    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK1(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))))),
% 1.51/0.98    introduced(choice_axiom,[])).
% 1.51/0.98  
% 1.51/0.98  fof(f35,plain,(
% 1.51/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK1(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK2(X0,X1,X2,X5)) & m1_subset_1(sK2(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.51/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f34,f33])).
% 1.51/0.98  
% 1.51/0.98  fof(f50,plain,(
% 1.51/0.98    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.51/0.98    inference(cnf_transformation,[],[f35])).
% 1.51/0.98  
% 1.51/0.98  fof(f2,axiom,(
% 1.51/0.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f41,plain,(
% 1.51/0.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.51/0.98    inference(cnf_transformation,[],[f2])).
% 1.51/0.98  
% 1.51/0.98  fof(f4,axiom,(
% 1.51/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f43,plain,(
% 1.51/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.51/0.98    inference(cnf_transformation,[],[f4])).
% 1.51/0.98  
% 1.51/0.98  fof(f62,plain,(
% 1.51/0.98    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 1.51/0.98    inference(definition_unfolding,[],[f41,f43])).
% 1.51/0.98  
% 1.51/0.98  fof(f10,axiom,(
% 1.51/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f23,plain,(
% 1.51/0.98    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.51/0.98    inference(ennf_transformation,[],[f10])).
% 1.51/0.98  
% 1.51/0.98  fof(f24,plain,(
% 1.51/0.98    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.51/0.98    inference(flattening,[],[f23])).
% 1.51/0.98  
% 1.51/0.98  fof(f36,plain,(
% 1.51/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.51/0.98    inference(nnf_transformation,[],[f24])).
% 1.51/0.98  
% 1.51/0.98  fof(f54,plain,(
% 1.51/0.98    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.51/0.98    inference(cnf_transformation,[],[f36])).
% 1.51/0.98  
% 1.51/0.98  fof(f12,conjecture,(
% 1.51/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f13,negated_conjecture,(
% 1.51/0.98    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.51/0.98    inference(negated_conjecture,[],[f12])).
% 1.51/0.98  
% 1.51/0.98  fof(f15,plain,(
% 1.51/0.98    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.51/0.98    inference(pure_predicate_removal,[],[f13])).
% 1.51/0.98  
% 1.51/0.98  fof(f16,plain,(
% 1.51/0.98    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.51/0.98    inference(pure_predicate_removal,[],[f15])).
% 1.51/0.98  
% 1.51/0.98  fof(f27,plain,(
% 1.51/0.98    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.51/0.98    inference(ennf_transformation,[],[f16])).
% 1.51/0.98  
% 1.51/0.98  fof(f28,plain,(
% 1.51/0.98    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.51/0.98    inference(flattening,[],[f27])).
% 1.51/0.98  
% 1.51/0.98  fof(f38,plain,(
% 1.51/0.98    ( ! [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (~r1_waybel_0(X0,sK4,u1_struct_0(X0)) & l1_waybel_0(sK4,X0) & ~v2_struct_0(sK4))) )),
% 1.51/0.98    introduced(choice_axiom,[])).
% 1.51/0.98  
% 1.51/0.98  fof(f37,plain,(
% 1.51/0.98    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK3,X1,u1_struct_0(sK3)) & l1_waybel_0(X1,sK3) & ~v2_struct_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 1.51/0.98    introduced(choice_axiom,[])).
% 1.51/0.98  
% 1.51/0.98  fof(f39,plain,(
% 1.51/0.98    (~r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) & l1_waybel_0(sK4,sK3) & ~v2_struct_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 1.51/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f38,f37])).
% 1.51/0.98  
% 1.51/0.98  fof(f61,plain,(
% 1.51/0.98    ~r1_waybel_0(sK3,sK4,u1_struct_0(sK3))),
% 1.51/0.98    inference(cnf_transformation,[],[f39])).
% 1.51/0.98  
% 1.51/0.98  fof(f3,axiom,(
% 1.51/0.98    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f29,plain,(
% 1.51/0.98    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 1.51/0.98    introduced(choice_axiom,[])).
% 1.51/0.98  
% 1.51/0.98  fof(f30,plain,(
% 1.51/0.98    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 1.51/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3,f29])).
% 1.51/0.98  
% 1.51/0.98  fof(f42,plain,(
% 1.51/0.98    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 1.51/0.98    inference(cnf_transformation,[],[f30])).
% 1.51/0.98  
% 1.51/0.98  fof(f5,axiom,(
% 1.51/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.51/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/0.98  
% 1.51/0.98  fof(f44,plain,(
% 1.51/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.51/0.98    inference(cnf_transformation,[],[f5])).
% 1.51/0.98  
% 1.51/0.98  fof(f60,plain,(
% 1.51/0.98    l1_waybel_0(sK4,sK3)),
% 1.51/0.98    inference(cnf_transformation,[],[f39])).
% 1.51/0.98  
% 1.51/0.98  fof(f59,plain,(
% 1.51/0.98    ~v2_struct_0(sK4)),
% 1.51/0.98    inference(cnf_transformation,[],[f39])).
% 1.51/0.98  
% 1.51/0.98  fof(f58,plain,(
% 1.51/0.98    l1_struct_0(sK3)),
% 1.51/0.98    inference(cnf_transformation,[],[f39])).
% 1.51/0.98  
% 1.51/0.98  fof(f57,plain,(
% 1.51/0.98    ~v2_struct_0(sK3)),
% 1.51/0.98    inference(cnf_transformation,[],[f39])).
% 1.51/0.98  
% 1.51/0.98  cnf(c_0,plain,
% 1.51/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 1.51/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_6,plain,
% 1.51/0.98      ( ~ r2_hidden(X0,X1)
% 1.51/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.51/0.98      | ~ v1_xboole_0(X2) ),
% 1.51/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_221,plain,
% 1.51/0.98      ( ~ r2_hidden(X0,X1)
% 1.51/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.51/0.98      | k1_xboole_0 != X2 ),
% 1.51/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_222,plain,
% 1.51/0.98      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
% 1.51/0.98      inference(unflattening,[status(thm)],[c_221]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1308,plain,
% 1.51/0.98      ( ~ r2_hidden(X0,k1_xboole_0)
% 1.51/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 1.51/0.98      inference(instantiation,[status(thm)],[c_222]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1697,plain,
% 1.51/0.98      ( ~ r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k1_xboole_0,sK0(u1_struct_0(sK4)))),k1_xboole_0)
% 1.51/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 1.51/0.98      inference(instantiation,[status(thm)],[c_1308]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_9,plain,
% 1.51/0.98      ( ~ r2_waybel_0(X0,X1,X2)
% 1.51/0.98      | ~ l1_waybel_0(X1,X0)
% 1.51/0.98      | r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
% 1.51/0.98      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.51/0.98      | ~ l1_struct_0(X0)
% 1.51/0.98      | v2_struct_0(X0)
% 1.51/0.98      | v2_struct_0(X1) ),
% 1.51/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1288,plain,
% 1.51/0.98      ( ~ r2_waybel_0(sK3,sK4,X0)
% 1.51/0.98      | ~ l1_waybel_0(sK4,sK3)
% 1.51/0.98      | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,X0,X1)),X0)
% 1.51/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.51/0.98      | ~ l1_struct_0(sK3)
% 1.51/0.98      | v2_struct_0(sK4)
% 1.51/0.98      | v2_struct_0(sK3) ),
% 1.51/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1418,plain,
% 1.51/0.98      ( ~ r2_waybel_0(sK3,sK4,X0)
% 1.51/0.98      | ~ l1_waybel_0(sK4,sK3)
% 1.51/0.98      | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,X0,sK0(u1_struct_0(sK4)))),X0)
% 1.51/0.98      | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
% 1.51/0.98      | ~ l1_struct_0(sK3)
% 1.51/0.98      | v2_struct_0(sK4)
% 1.51/0.98      | v2_struct_0(sK3) ),
% 1.51/0.98      inference(instantiation,[status(thm)],[c_1288]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1696,plain,
% 1.51/0.98      ( ~ r2_waybel_0(sK3,sK4,k1_xboole_0)
% 1.51/0.98      | ~ l1_waybel_0(sK4,sK3)
% 1.51/0.98      | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k1_xboole_0,sK0(u1_struct_0(sK4)))),k1_xboole_0)
% 1.51/0.98      | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
% 1.51/0.98      | ~ l1_struct_0(sK3)
% 1.51/0.98      | v2_struct_0(sK4)
% 1.51/0.98      | v2_struct_0(sK3) ),
% 1.51/0.98      inference(instantiation,[status(thm)],[c_1418]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1,plain,
% 1.51/0.98      ( k6_subset_1(X0,k1_xboole_0) = X0 ),
% 1.51/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_12,plain,
% 1.51/0.98      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 1.51/0.98      | r2_waybel_0(X0,X1,X2)
% 1.51/0.98      | ~ l1_waybel_0(X1,X0)
% 1.51/0.98      | ~ l1_struct_0(X0)
% 1.51/0.98      | v2_struct_0(X0)
% 1.51/0.98      | v2_struct_0(X1) ),
% 1.51/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1068,plain,
% 1.51/0.98      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) = iProver_top
% 1.51/0.98      | r2_waybel_0(X0,X1,X2) = iProver_top
% 1.51/0.98      | l1_waybel_0(X1,X0) != iProver_top
% 1.51/0.98      | l1_struct_0(X0) != iProver_top
% 1.51/0.98      | v2_struct_0(X0) = iProver_top
% 1.51/0.98      | v2_struct_0(X1) = iProver_top ),
% 1.51/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1523,plain,
% 1.51/0.98      ( r1_waybel_0(X0,X1,u1_struct_0(X0)) = iProver_top
% 1.51/0.98      | r2_waybel_0(X0,X1,k1_xboole_0) = iProver_top
% 1.51/0.98      | l1_waybel_0(X1,X0) != iProver_top
% 1.51/0.98      | l1_struct_0(X0) != iProver_top
% 1.51/0.98      | v2_struct_0(X0) = iProver_top
% 1.51/0.98      | v2_struct_0(X1) = iProver_top ),
% 1.51/0.98      inference(superposition,[status(thm)],[c_1,c_1068]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_16,negated_conjecture,
% 1.51/0.98      ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) ),
% 1.51/0.98      inference(cnf_transformation,[],[f61]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1066,plain,
% 1.51/0.98      ( r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.51/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1534,plain,
% 1.51/0.98      ( r2_waybel_0(sK3,sK4,k1_xboole_0) = iProver_top
% 1.51/0.98      | l1_waybel_0(sK4,sK3) != iProver_top
% 1.51/0.98      | l1_struct_0(sK3) != iProver_top
% 1.51/0.98      | v2_struct_0(sK4) = iProver_top
% 1.51/0.98      | v2_struct_0(sK3) = iProver_top ),
% 1.51/0.98      inference(superposition,[status(thm)],[c_1523,c_1066]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1535,plain,
% 1.51/0.98      ( r2_waybel_0(sK3,sK4,k1_xboole_0)
% 1.51/0.98      | ~ l1_waybel_0(sK4,sK3)
% 1.51/0.98      | ~ l1_struct_0(sK3)
% 1.51/0.98      | v2_struct_0(sK4)
% 1.51/0.98      | v2_struct_0(sK3) ),
% 1.51/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1534]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_2,plain,
% 1.51/0.98      ( m1_subset_1(sK0(X0),X0) ),
% 1.51/0.98      inference(cnf_transformation,[],[f42]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1342,plain,
% 1.51/0.98      ( m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) ),
% 1.51/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_3,plain,
% 1.51/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.51/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_1309,plain,
% 1.51/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 1.51/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_17,negated_conjecture,
% 1.51/0.98      ( l1_waybel_0(sK4,sK3) ),
% 1.51/0.98      inference(cnf_transformation,[],[f60]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_18,negated_conjecture,
% 1.51/0.98      ( ~ v2_struct_0(sK4) ),
% 1.51/0.98      inference(cnf_transformation,[],[f59]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_19,negated_conjecture,
% 1.51/0.98      ( l1_struct_0(sK3) ),
% 1.51/0.98      inference(cnf_transformation,[],[f58]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(c_20,negated_conjecture,
% 1.51/0.98      ( ~ v2_struct_0(sK3) ),
% 1.51/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.51/0.98  
% 1.51/0.98  cnf(contradiction,plain,
% 1.51/0.98      ( $false ),
% 1.51/0.98      inference(minisat,
% 1.51/0.98                [status(thm)],
% 1.51/0.98                [c_1697,c_1696,c_1535,c_1342,c_1309,c_17,c_18,c_19,c_20]) ).
% 1.51/0.98  
% 1.51/0.98  
% 1.51/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.51/0.98  
% 1.51/0.98  ------                               Statistics
% 1.51/0.98  
% 1.51/0.98  ------ General
% 1.51/0.98  
% 1.51/0.98  abstr_ref_over_cycles:                  0
% 1.51/0.98  abstr_ref_under_cycles:                 0
% 1.51/0.98  gc_basic_clause_elim:                   0
% 1.51/0.98  forced_gc_time:                         0
% 1.51/0.98  parsing_time:                           0.01
% 1.51/0.98  unif_index_cands_time:                  0.
% 1.51/0.98  unif_index_add_time:                    0.
% 1.51/0.98  orderings_time:                         0.
% 1.51/0.98  out_proof_time:                         0.009
% 1.51/0.98  total_time:                             0.09
% 1.51/0.98  num_of_symbols:                         51
% 1.51/0.98  num_of_terms:                           1590
% 1.51/0.98  
% 1.51/0.98  ------ Preprocessing
% 1.51/0.98  
% 1.51/0.98  num_of_splits:                          0
% 1.51/0.98  num_of_split_atoms:                     0
% 1.51/0.98  num_of_reused_defs:                     0
% 1.51/0.98  num_eq_ax_congr_red:                    44
% 1.51/0.98  num_of_sem_filtered_clauses:            1
% 1.51/0.98  num_of_subtypes:                        0
% 1.51/0.98  monotx_restored_types:                  0
% 1.51/0.98  sat_num_of_epr_types:                   0
% 1.51/0.98  sat_num_of_non_cyclic_types:            0
% 1.51/0.98  sat_guarded_non_collapsed_types:        0
% 1.51/0.98  num_pure_diseq_elim:                    0
% 1.51/0.98  simp_replaced_by:                       0
% 1.51/0.98  res_preprocessed:                       102
% 1.51/0.98  prep_upred:                             0
% 1.51/0.98  prep_unflattend:                        18
% 1.51/0.98  smt_new_axioms:                         0
% 1.51/0.98  pred_elim_cands:                        7
% 1.51/0.98  pred_elim:                              3
% 1.51/0.98  pred_elim_cl:                           3
% 1.51/0.98  pred_elim_cycles:                       5
% 1.51/0.98  merged_defs:                            0
% 1.51/0.98  merged_defs_ncl:                        0
% 1.51/0.98  bin_hyper_res:                          0
% 1.51/0.98  prep_cycles:                            4
% 1.51/0.98  pred_elim_time:                         0.008
% 1.51/0.98  splitting_time:                         0.
% 1.51/0.98  sem_filter_time:                        0.
% 1.51/0.98  monotx_time:                            0.001
% 1.51/0.98  subtype_inf_time:                       0.
% 1.51/0.98  
% 1.51/0.98  ------ Problem properties
% 1.51/0.98  
% 1.51/0.98  clauses:                                18
% 1.51/0.98  conjectures:                            5
% 1.51/0.98  epr:                                    4
% 1.51/0.98  horn:                                   10
% 1.51/0.98  ground:                                 5
% 1.51/0.98  unary:                                  8
% 1.51/0.98  binary:                                 1
% 1.51/0.98  lits:                                   69
% 1.51/0.98  lits_eq:                                1
% 1.51/0.98  fd_pure:                                0
% 1.51/0.98  fd_pseudo:                              0
% 1.51/0.98  fd_cond:                                0
% 1.51/0.98  fd_pseudo_cond:                         0
% 1.51/0.98  ac_symbols:                             0
% 1.51/0.98  
% 1.51/0.98  ------ Propositional Solver
% 1.51/0.98  
% 1.51/0.98  prop_solver_calls:                      25
% 1.51/0.98  prop_fast_solver_calls:                 852
% 1.51/0.98  smt_solver_calls:                       0
% 1.51/0.98  smt_fast_solver_calls:                  0
% 1.51/0.98  prop_num_of_clauses:                    401
% 1.51/0.98  prop_preprocess_simplified:             2877
% 1.51/0.98  prop_fo_subsumed:                       4
% 1.51/0.98  prop_solver_time:                       0.
% 1.51/0.98  smt_solver_time:                        0.
% 1.51/0.98  smt_fast_solver_time:                   0.
% 1.51/0.98  prop_fast_solver_time:                  0.
% 1.51/0.98  prop_unsat_core_time:                   0.
% 1.51/0.98  
% 1.51/0.98  ------ QBF
% 1.51/0.98  
% 1.51/0.98  qbf_q_res:                              0
% 1.51/0.98  qbf_num_tautologies:                    0
% 1.51/0.98  qbf_prep_cycles:                        0
% 1.51/0.98  
% 1.51/0.98  ------ BMC1
% 1.51/0.98  
% 1.51/0.98  bmc1_current_bound:                     -1
% 1.51/0.98  bmc1_last_solved_bound:                 -1
% 1.51/0.98  bmc1_unsat_core_size:                   -1
% 1.51/0.98  bmc1_unsat_core_parents_size:           -1
% 1.51/0.98  bmc1_merge_next_fun:                    0
% 1.51/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.51/0.98  
% 1.51/0.98  ------ Instantiation
% 1.51/0.98  
% 1.51/0.98  inst_num_of_clauses:                    120
% 1.51/0.98  inst_num_in_passive:                    43
% 1.51/0.98  inst_num_in_active:                     65
% 1.51/0.98  inst_num_in_unprocessed:                11
% 1.51/0.98  inst_num_of_loops:                      80
% 1.51/0.98  inst_num_of_learning_restarts:          0
% 1.51/0.98  inst_num_moves_active_passive:          11
% 1.51/0.98  inst_lit_activity:                      0
% 1.51/0.98  inst_lit_activity_moves:                0
% 1.51/0.98  inst_num_tautologies:                   0
% 1.51/0.98  inst_num_prop_implied:                  0
% 1.51/0.98  inst_num_existing_simplified:           0
% 1.51/0.98  inst_num_eq_res_simplified:             0
% 1.51/0.98  inst_num_child_elim:                    0
% 1.51/0.98  inst_num_of_dismatching_blockings:      3
% 1.51/0.98  inst_num_of_non_proper_insts:           48
% 1.51/0.98  inst_num_of_duplicates:                 0
% 1.51/0.98  inst_inst_num_from_inst_to_res:         0
% 1.51/0.98  inst_dismatching_checking_time:         0.
% 1.51/0.98  
% 1.51/0.98  ------ Resolution
% 1.51/0.98  
% 1.51/0.98  res_num_of_clauses:                     0
% 1.51/0.98  res_num_in_passive:                     0
% 1.51/0.98  res_num_in_active:                      0
% 1.51/0.98  res_num_of_loops:                       106
% 1.51/0.98  res_forward_subset_subsumed:            1
% 1.51/0.98  res_backward_subset_subsumed:           0
% 1.51/0.98  res_forward_subsumed:                   0
% 1.51/0.98  res_backward_subsumed:                  0
% 1.51/0.98  res_forward_subsumption_resolution:     2
% 1.51/0.98  res_backward_subsumption_resolution:    0
% 1.51/0.98  res_clause_to_clause_subsumption:       23
% 1.51/0.98  res_orphan_elimination:                 0
% 1.51/0.98  res_tautology_del:                      6
% 1.51/0.98  res_num_eq_res_simplified:              0
% 1.51/0.98  res_num_sel_changes:                    0
% 1.51/0.98  res_moves_from_active_to_pass:          0
% 1.51/0.98  
% 1.51/0.98  ------ Superposition
% 1.51/0.98  
% 1.51/0.98  sup_time_total:                         0.
% 1.51/0.98  sup_time_generating:                    0.
% 1.51/0.98  sup_time_sim_full:                      0.
% 1.51/0.98  sup_time_sim_immed:                     0.
% 1.51/0.98  
% 1.51/0.98  sup_num_of_clauses:                     23
% 1.51/0.98  sup_num_in_active:                      14
% 1.51/0.98  sup_num_in_passive:                     9
% 1.51/0.98  sup_num_of_loops:                       14
% 1.51/0.98  sup_fw_superposition:                   3
% 1.51/0.98  sup_bw_superposition:                   2
% 1.51/0.98  sup_immediate_simplified:               0
% 1.51/0.98  sup_given_eliminated:                   0
% 1.51/0.98  comparisons_done:                       0
% 1.51/0.98  comparisons_avoided:                    0
% 1.51/0.98  
% 1.51/0.98  ------ Simplifications
% 1.51/0.98  
% 1.51/0.98  
% 1.51/0.98  sim_fw_subset_subsumed:                 0
% 1.51/0.98  sim_bw_subset_subsumed:                 0
% 1.51/0.98  sim_fw_subsumed:                        0
% 1.51/0.98  sim_bw_subsumed:                        0
% 1.51/0.98  sim_fw_subsumption_res:                 0
% 1.51/0.98  sim_bw_subsumption_res:                 0
% 1.51/0.98  sim_tautology_del:                      0
% 1.51/0.98  sim_eq_tautology_del:                   0
% 1.51/0.98  sim_eq_res_simp:                        0
% 1.51/0.98  sim_fw_demodulated:                     0
% 1.51/0.98  sim_bw_demodulated:                     0
% 1.51/0.98  sim_light_normalised:                   0
% 1.51/0.98  sim_joinable_taut:                      0
% 1.51/0.98  sim_joinable_simp:                      0
% 1.51/0.98  sim_ac_normalised:                      0
% 1.51/0.98  sim_smt_subsumption:                    0
% 1.51/0.98  
%------------------------------------------------------------------------------
