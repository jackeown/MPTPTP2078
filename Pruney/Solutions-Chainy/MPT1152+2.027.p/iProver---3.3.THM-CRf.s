%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:15 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  141 (1377 expanded)
%              Number of clauses        :   86 ( 386 expanded)
%              Number of leaves         :   16 ( 299 expanded)
%              Depth                    :   20
%              Number of atoms          :  583 (6654 expanded)
%              Number of equality atoms :  153 (1219 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f25,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f36,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f36])).

fof(f60,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f27])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X3,X4)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X5,X6)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f31])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK2(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
                & r2_hidden(sK1(X1,X2,X3),X2)
                & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK2(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK2(X0,X1,X2) = X0
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f34,f33])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X1,sK2(X0,X1,X2),X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
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

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_297,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_11,c_5])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_664,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_297,c_19])).

cnf(c_665,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_1149,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_308,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_11,c_4])).

cnf(c_659,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_308,c_19])).

cnf(c_660,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_659])).

cnf(c_1165,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1149,c_660])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_581,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK3)
    | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_586,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_582,c_23,c_22,c_21,c_19])).

cnf(c_1151,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_1182,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1151,c_660])).

cnf(c_1353,plain,
    ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1165,c_1182])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1158,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK2(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK2(X2,X1,X0) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK3)
    | sK2(X1,sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
    | sK2(X1,sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_23,c_22,c_21,c_19])).

cnf(c_1154,plain,
    ( sK2(X0,sK3,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(c_1199,plain,
    ( sK2(X0,sK3,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1154,c_660])).

cnf(c_1516,plain,
    ( sK2(sK0(a_2_1_orders_2(sK3,X0)),sK3,X0) = sK0(a_2_1_orders_2(sK3,X0))
    | a_2_1_orders_2(sK3,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1158,c_1199])).

cnf(c_1580,plain,
    ( sK2(sK0(a_2_1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(a_2_1_orders_2(sK3,k2_struct_0(sK3)))
    | a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1165,c_1516])).

cnf(c_1872,plain,
    ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
    | k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1353,c_1580])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_48,plain,
    ( ~ l1_orders_2(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_66,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1298,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_586])).

cnf(c_1313,plain,
    ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
    | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_897,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1336,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
    | X1 != k2_orders_2(sK3,k2_struct_0(sK3))
    | X0 != sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_897])).

cnf(c_1483,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3)))
    | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
    | X0 != sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
    | a_2_1_orders_2(sK3,k2_struct_0(sK3)) != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1336])).

cnf(c_1670,plain,
    ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3)))
    | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
    | a_2_1_orders_2(sK3,k2_struct_0(sK3)) != k2_orders_2(sK3,k2_struct_0(sK3))
    | sK0(k2_orders_2(sK3,k2_struct_0(sK3))) != sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_895,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1671,plain,
    ( sK0(k2_orders_2(sK3,k2_struct_0(sK3))) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_1306,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3)))
    | sK2(X0,sK3,k2_struct_0(sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_1969,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3)))
    | sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1306])).

cnf(c_2127,plain,
    ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1872,c_19,c_18,c_48,c_66,c_1298,c_1313,c_1670,c_1671,c_1969])).

cnf(c_15,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_440,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_441,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_445,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_441,c_23,c_22,c_21,c_19])).

cnf(c_1157,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_1240,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1157,c_660])).

cnf(c_8,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_671,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_672,plain,
    ( ~ r2_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_671])).

cnf(c_1148,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_672])).

cnf(c_1177,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1148,c_660])).

cnf(c_1742,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1240,c_1177])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_23,c_22,c_21,c_19])).

cnf(c_1155,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_1206,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1155,c_660])).

cnf(c_2008,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1742,c_1206])).

cnf(c_2131,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2127,c_2008])).

cnf(c_2151,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2131,c_1353])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_283,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_11,c_6])).

cnf(c_631,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_283,c_23])).

cnf(c_632,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_63,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_634,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_632,c_23,c_19,c_48,c_63])).

cnf(c_644,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_634])).

cnf(c_645,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_1150,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_1172,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1150,c_660])).

cnf(c_1441,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1206,c_1172])).

cnf(c_2132,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2127,c_1441])).

cnf(c_2144,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2132,c_1353])).

cnf(c_2155,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2151,c_2144])).

cnf(c_1314,plain,
    ( k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3))
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1313])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2155,c_1314,c_1165,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:16:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.15/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.00  
% 2.15/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.15/1.00  
% 2.15/1.00  ------  iProver source info
% 2.15/1.00  
% 2.15/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.15/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.15/1.00  git: non_committed_changes: false
% 2.15/1.00  git: last_make_outside_of_git: false
% 2.15/1.00  
% 2.15/1.00  ------ 
% 2.15/1.00  
% 2.15/1.00  ------ Input Options
% 2.15/1.00  
% 2.15/1.00  --out_options                           all
% 2.15/1.00  --tptp_safe_out                         true
% 2.15/1.00  --problem_path                          ""
% 2.15/1.00  --include_path                          ""
% 2.15/1.00  --clausifier                            res/vclausify_rel
% 2.15/1.00  --clausifier_options                    --mode clausify
% 2.15/1.00  --stdin                                 false
% 2.15/1.00  --stats_out                             all
% 2.15/1.00  
% 2.15/1.00  ------ General Options
% 2.15/1.00  
% 2.15/1.00  --fof                                   false
% 2.15/1.00  --time_out_real                         305.
% 2.15/1.00  --time_out_virtual                      -1.
% 2.15/1.00  --symbol_type_check                     false
% 2.15/1.00  --clausify_out                          false
% 2.15/1.00  --sig_cnt_out                           false
% 2.15/1.00  --trig_cnt_out                          false
% 2.15/1.00  --trig_cnt_out_tolerance                1.
% 2.15/1.00  --trig_cnt_out_sk_spl                   false
% 2.15/1.00  --abstr_cl_out                          false
% 2.15/1.00  
% 2.15/1.00  ------ Global Options
% 2.15/1.00  
% 2.15/1.00  --schedule                              default
% 2.15/1.00  --add_important_lit                     false
% 2.15/1.00  --prop_solver_per_cl                    1000
% 2.15/1.00  --min_unsat_core                        false
% 2.15/1.00  --soft_assumptions                      false
% 2.15/1.00  --soft_lemma_size                       3
% 2.15/1.00  --prop_impl_unit_size                   0
% 2.15/1.00  --prop_impl_unit                        []
% 2.15/1.00  --share_sel_clauses                     true
% 2.15/1.00  --reset_solvers                         false
% 2.15/1.00  --bc_imp_inh                            [conj_cone]
% 2.15/1.00  --conj_cone_tolerance                   3.
% 2.15/1.00  --extra_neg_conj                        none
% 2.15/1.00  --large_theory_mode                     true
% 2.15/1.00  --prolific_symb_bound                   200
% 2.15/1.00  --lt_threshold                          2000
% 2.15/1.00  --clause_weak_htbl                      true
% 2.15/1.00  --gc_record_bc_elim                     false
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing Options
% 2.15/1.00  
% 2.15/1.00  --preprocessing_flag                    true
% 2.15/1.00  --time_out_prep_mult                    0.1
% 2.15/1.00  --splitting_mode                        input
% 2.15/1.00  --splitting_grd                         true
% 2.15/1.00  --splitting_cvd                         false
% 2.15/1.00  --splitting_cvd_svl                     false
% 2.15/1.00  --splitting_nvd                         32
% 2.15/1.00  --sub_typing                            true
% 2.15/1.00  --prep_gs_sim                           true
% 2.15/1.00  --prep_unflatten                        true
% 2.15/1.00  --prep_res_sim                          true
% 2.15/1.00  --prep_upred                            true
% 2.15/1.00  --prep_sem_filter                       exhaustive
% 2.15/1.00  --prep_sem_filter_out                   false
% 2.15/1.00  --pred_elim                             true
% 2.15/1.00  --res_sim_input                         true
% 2.15/1.00  --eq_ax_congr_red                       true
% 2.15/1.00  --pure_diseq_elim                       true
% 2.15/1.00  --brand_transform                       false
% 2.15/1.00  --non_eq_to_eq                          false
% 2.15/1.00  --prep_def_merge                        true
% 2.15/1.00  --prep_def_merge_prop_impl              false
% 2.15/1.00  --prep_def_merge_mbd                    true
% 2.15/1.00  --prep_def_merge_tr_red                 false
% 2.15/1.00  --prep_def_merge_tr_cl                  false
% 2.15/1.00  --smt_preprocessing                     true
% 2.15/1.00  --smt_ac_axioms                         fast
% 2.15/1.00  --preprocessed_out                      false
% 2.15/1.00  --preprocessed_stats                    false
% 2.15/1.00  
% 2.15/1.00  ------ Abstraction refinement Options
% 2.15/1.00  
% 2.15/1.00  --abstr_ref                             []
% 2.15/1.00  --abstr_ref_prep                        false
% 2.15/1.00  --abstr_ref_until_sat                   false
% 2.15/1.00  --abstr_ref_sig_restrict                funpre
% 2.15/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/1.00  --abstr_ref_under                       []
% 2.15/1.00  
% 2.15/1.00  ------ SAT Options
% 2.15/1.00  
% 2.15/1.00  --sat_mode                              false
% 2.15/1.00  --sat_fm_restart_options                ""
% 2.15/1.00  --sat_gr_def                            false
% 2.15/1.00  --sat_epr_types                         true
% 2.15/1.00  --sat_non_cyclic_types                  false
% 2.15/1.00  --sat_finite_models                     false
% 2.15/1.00  --sat_fm_lemmas                         false
% 2.15/1.00  --sat_fm_prep                           false
% 2.15/1.00  --sat_fm_uc_incr                        true
% 2.15/1.00  --sat_out_model                         small
% 2.15/1.00  --sat_out_clauses                       false
% 2.15/1.00  
% 2.15/1.00  ------ QBF Options
% 2.15/1.00  
% 2.15/1.00  --qbf_mode                              false
% 2.15/1.00  --qbf_elim_univ                         false
% 2.15/1.00  --qbf_dom_inst                          none
% 2.15/1.00  --qbf_dom_pre_inst                      false
% 2.15/1.00  --qbf_sk_in                             false
% 2.15/1.00  --qbf_pred_elim                         true
% 2.15/1.00  --qbf_split                             512
% 2.15/1.00  
% 2.15/1.00  ------ BMC1 Options
% 2.15/1.00  
% 2.15/1.00  --bmc1_incremental                      false
% 2.15/1.00  --bmc1_axioms                           reachable_all
% 2.15/1.00  --bmc1_min_bound                        0
% 2.15/1.00  --bmc1_max_bound                        -1
% 2.15/1.00  --bmc1_max_bound_default                -1
% 2.15/1.00  --bmc1_symbol_reachability              true
% 2.15/1.00  --bmc1_property_lemmas                  false
% 2.15/1.00  --bmc1_k_induction                      false
% 2.15/1.00  --bmc1_non_equiv_states                 false
% 2.15/1.00  --bmc1_deadlock                         false
% 2.15/1.00  --bmc1_ucm                              false
% 2.15/1.00  --bmc1_add_unsat_core                   none
% 2.15/1.00  --bmc1_unsat_core_children              false
% 2.15/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/1.00  --bmc1_out_stat                         full
% 2.15/1.00  --bmc1_ground_init                      false
% 2.15/1.00  --bmc1_pre_inst_next_state              false
% 2.15/1.00  --bmc1_pre_inst_state                   false
% 2.15/1.00  --bmc1_pre_inst_reach_state             false
% 2.15/1.00  --bmc1_out_unsat_core                   false
% 2.15/1.00  --bmc1_aig_witness_out                  false
% 2.15/1.00  --bmc1_verbose                          false
% 2.15/1.00  --bmc1_dump_clauses_tptp                false
% 2.15/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.15/1.00  --bmc1_dump_file                        -
% 2.15/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.15/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.15/1.00  --bmc1_ucm_extend_mode                  1
% 2.15/1.00  --bmc1_ucm_init_mode                    2
% 2.15/1.00  --bmc1_ucm_cone_mode                    none
% 2.15/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.15/1.00  --bmc1_ucm_relax_model                  4
% 2.15/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.15/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/1.00  --bmc1_ucm_layered_model                none
% 2.15/1.00  --bmc1_ucm_max_lemma_size               10
% 2.15/1.00  
% 2.15/1.00  ------ AIG Options
% 2.15/1.00  
% 2.15/1.00  --aig_mode                              false
% 2.15/1.00  
% 2.15/1.00  ------ Instantiation Options
% 2.15/1.00  
% 2.15/1.00  --instantiation_flag                    true
% 2.15/1.00  --inst_sos_flag                         false
% 2.15/1.00  --inst_sos_phase                        true
% 2.15/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/1.00  --inst_lit_sel_side                     num_symb
% 2.15/1.00  --inst_solver_per_active                1400
% 2.15/1.00  --inst_solver_calls_frac                1.
% 2.15/1.00  --inst_passive_queue_type               priority_queues
% 2.15/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/1.00  --inst_passive_queues_freq              [25;2]
% 2.15/1.00  --inst_dismatching                      true
% 2.15/1.00  --inst_eager_unprocessed_to_passive     true
% 2.15/1.00  --inst_prop_sim_given                   true
% 2.15/1.00  --inst_prop_sim_new                     false
% 2.15/1.00  --inst_subs_new                         false
% 2.15/1.00  --inst_eq_res_simp                      false
% 2.15/1.00  --inst_subs_given                       false
% 2.15/1.00  --inst_orphan_elimination               true
% 2.15/1.00  --inst_learning_loop_flag               true
% 2.15/1.00  --inst_learning_start                   3000
% 2.15/1.00  --inst_learning_factor                  2
% 2.15/1.00  --inst_start_prop_sim_after_learn       3
% 2.15/1.00  --inst_sel_renew                        solver
% 2.15/1.00  --inst_lit_activity_flag                true
% 2.15/1.00  --inst_restr_to_given                   false
% 2.15/1.00  --inst_activity_threshold               500
% 2.15/1.00  --inst_out_proof                        true
% 2.15/1.00  
% 2.15/1.00  ------ Resolution Options
% 2.15/1.00  
% 2.15/1.00  --resolution_flag                       true
% 2.15/1.00  --res_lit_sel                           adaptive
% 2.15/1.00  --res_lit_sel_side                      none
% 2.15/1.00  --res_ordering                          kbo
% 2.15/1.00  --res_to_prop_solver                    active
% 2.15/1.00  --res_prop_simpl_new                    false
% 2.15/1.00  --res_prop_simpl_given                  true
% 2.15/1.00  --res_passive_queue_type                priority_queues
% 2.15/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/1.00  --res_passive_queues_freq               [15;5]
% 2.15/1.00  --res_forward_subs                      full
% 2.15/1.00  --res_backward_subs                     full
% 2.15/1.00  --res_forward_subs_resolution           true
% 2.15/1.00  --res_backward_subs_resolution          true
% 2.15/1.00  --res_orphan_elimination                true
% 2.15/1.00  --res_time_limit                        2.
% 2.15/1.00  --res_out_proof                         true
% 2.15/1.00  
% 2.15/1.00  ------ Superposition Options
% 2.15/1.00  
% 2.15/1.00  --superposition_flag                    true
% 2.15/1.00  --sup_passive_queue_type                priority_queues
% 2.15/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.15/1.00  --demod_completeness_check              fast
% 2.15/1.00  --demod_use_ground                      true
% 2.15/1.00  --sup_to_prop_solver                    passive
% 2.15/1.00  --sup_prop_simpl_new                    true
% 2.15/1.00  --sup_prop_simpl_given                  true
% 2.15/1.00  --sup_fun_splitting                     false
% 2.15/1.00  --sup_smt_interval                      50000
% 2.15/1.00  
% 2.15/1.00  ------ Superposition Simplification Setup
% 2.15/1.00  
% 2.15/1.00  --sup_indices_passive                   []
% 2.15/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_full_bw                           [BwDemod]
% 2.15/1.00  --sup_immed_triv                        [TrivRules]
% 2.15/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_immed_bw_main                     []
% 2.15/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.00  
% 2.15/1.00  ------ Combination Options
% 2.15/1.00  
% 2.15/1.00  --comb_res_mult                         3
% 2.15/1.00  --comb_sup_mult                         2
% 2.15/1.00  --comb_inst_mult                        10
% 2.15/1.00  
% 2.15/1.00  ------ Debug Options
% 2.15/1.00  
% 2.15/1.00  --dbg_backtrace                         false
% 2.15/1.00  --dbg_dump_prop_clauses                 false
% 2.15/1.00  --dbg_dump_prop_clauses_file            -
% 2.15/1.00  --dbg_out_stat                          false
% 2.15/1.00  ------ Parsing...
% 2.15/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.15/1.00  ------ Proving...
% 2.15/1.00  ------ Problem Properties 
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  clauses                                 15
% 2.15/1.00  conjectures                             1
% 2.15/1.00  EPR                                     0
% 2.15/1.00  Horn                                    12
% 2.15/1.00  unary                                   3
% 2.15/1.00  binary                                  4
% 2.15/1.00  lits                                    40
% 2.15/1.00  lits eq                                 9
% 2.15/1.00  fd_pure                                 0
% 2.15/1.00  fd_pseudo                               0
% 2.15/1.00  fd_cond                                 3
% 2.15/1.00  fd_pseudo_cond                          0
% 2.15/1.00  AC symbols                              0
% 2.15/1.00  
% 2.15/1.00  ------ Schedule dynamic 5 is on 
% 2.15/1.00  
% 2.15/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  ------ 
% 2.15/1.00  Current options:
% 2.15/1.00  ------ 
% 2.15/1.00  
% 2.15/1.00  ------ Input Options
% 2.15/1.00  
% 2.15/1.00  --out_options                           all
% 2.15/1.00  --tptp_safe_out                         true
% 2.15/1.00  --problem_path                          ""
% 2.15/1.00  --include_path                          ""
% 2.15/1.00  --clausifier                            res/vclausify_rel
% 2.15/1.00  --clausifier_options                    --mode clausify
% 2.15/1.00  --stdin                                 false
% 2.15/1.00  --stats_out                             all
% 2.15/1.00  
% 2.15/1.00  ------ General Options
% 2.15/1.00  
% 2.15/1.00  --fof                                   false
% 2.15/1.00  --time_out_real                         305.
% 2.15/1.00  --time_out_virtual                      -1.
% 2.15/1.00  --symbol_type_check                     false
% 2.15/1.00  --clausify_out                          false
% 2.15/1.00  --sig_cnt_out                           false
% 2.15/1.00  --trig_cnt_out                          false
% 2.15/1.00  --trig_cnt_out_tolerance                1.
% 2.15/1.00  --trig_cnt_out_sk_spl                   false
% 2.15/1.00  --abstr_cl_out                          false
% 2.15/1.00  
% 2.15/1.00  ------ Global Options
% 2.15/1.00  
% 2.15/1.00  --schedule                              default
% 2.15/1.00  --add_important_lit                     false
% 2.15/1.00  --prop_solver_per_cl                    1000
% 2.15/1.00  --min_unsat_core                        false
% 2.15/1.00  --soft_assumptions                      false
% 2.15/1.00  --soft_lemma_size                       3
% 2.15/1.00  --prop_impl_unit_size                   0
% 2.15/1.00  --prop_impl_unit                        []
% 2.15/1.00  --share_sel_clauses                     true
% 2.15/1.00  --reset_solvers                         false
% 2.15/1.00  --bc_imp_inh                            [conj_cone]
% 2.15/1.00  --conj_cone_tolerance                   3.
% 2.15/1.00  --extra_neg_conj                        none
% 2.15/1.00  --large_theory_mode                     true
% 2.15/1.00  --prolific_symb_bound                   200
% 2.15/1.00  --lt_threshold                          2000
% 2.15/1.00  --clause_weak_htbl                      true
% 2.15/1.00  --gc_record_bc_elim                     false
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing Options
% 2.15/1.00  
% 2.15/1.00  --preprocessing_flag                    true
% 2.15/1.00  --time_out_prep_mult                    0.1
% 2.15/1.00  --splitting_mode                        input
% 2.15/1.00  --splitting_grd                         true
% 2.15/1.00  --splitting_cvd                         false
% 2.15/1.00  --splitting_cvd_svl                     false
% 2.15/1.00  --splitting_nvd                         32
% 2.15/1.00  --sub_typing                            true
% 2.15/1.00  --prep_gs_sim                           true
% 2.15/1.00  --prep_unflatten                        true
% 2.15/1.00  --prep_res_sim                          true
% 2.15/1.00  --prep_upred                            true
% 2.15/1.00  --prep_sem_filter                       exhaustive
% 2.15/1.00  --prep_sem_filter_out                   false
% 2.15/1.00  --pred_elim                             true
% 2.15/1.00  --res_sim_input                         true
% 2.15/1.00  --eq_ax_congr_red                       true
% 2.15/1.00  --pure_diseq_elim                       true
% 2.15/1.00  --brand_transform                       false
% 2.15/1.00  --non_eq_to_eq                          false
% 2.15/1.00  --prep_def_merge                        true
% 2.15/1.00  --prep_def_merge_prop_impl              false
% 2.15/1.00  --prep_def_merge_mbd                    true
% 2.15/1.00  --prep_def_merge_tr_red                 false
% 2.15/1.00  --prep_def_merge_tr_cl                  false
% 2.15/1.00  --smt_preprocessing                     true
% 2.15/1.00  --smt_ac_axioms                         fast
% 2.15/1.00  --preprocessed_out                      false
% 2.15/1.00  --preprocessed_stats                    false
% 2.15/1.00  
% 2.15/1.00  ------ Abstraction refinement Options
% 2.15/1.00  
% 2.15/1.00  --abstr_ref                             []
% 2.15/1.00  --abstr_ref_prep                        false
% 2.15/1.00  --abstr_ref_until_sat                   false
% 2.15/1.00  --abstr_ref_sig_restrict                funpre
% 2.15/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/1.00  --abstr_ref_under                       []
% 2.15/1.00  
% 2.15/1.00  ------ SAT Options
% 2.15/1.00  
% 2.15/1.00  --sat_mode                              false
% 2.15/1.00  --sat_fm_restart_options                ""
% 2.15/1.00  --sat_gr_def                            false
% 2.15/1.00  --sat_epr_types                         true
% 2.15/1.00  --sat_non_cyclic_types                  false
% 2.15/1.00  --sat_finite_models                     false
% 2.15/1.00  --sat_fm_lemmas                         false
% 2.15/1.00  --sat_fm_prep                           false
% 2.15/1.00  --sat_fm_uc_incr                        true
% 2.15/1.00  --sat_out_model                         small
% 2.15/1.00  --sat_out_clauses                       false
% 2.15/1.00  
% 2.15/1.00  ------ QBF Options
% 2.15/1.00  
% 2.15/1.00  --qbf_mode                              false
% 2.15/1.00  --qbf_elim_univ                         false
% 2.15/1.00  --qbf_dom_inst                          none
% 2.15/1.00  --qbf_dom_pre_inst                      false
% 2.15/1.00  --qbf_sk_in                             false
% 2.15/1.00  --qbf_pred_elim                         true
% 2.15/1.00  --qbf_split                             512
% 2.15/1.00  
% 2.15/1.00  ------ BMC1 Options
% 2.15/1.00  
% 2.15/1.00  --bmc1_incremental                      false
% 2.15/1.00  --bmc1_axioms                           reachable_all
% 2.15/1.00  --bmc1_min_bound                        0
% 2.15/1.00  --bmc1_max_bound                        -1
% 2.15/1.00  --bmc1_max_bound_default                -1
% 2.15/1.00  --bmc1_symbol_reachability              true
% 2.15/1.00  --bmc1_property_lemmas                  false
% 2.15/1.00  --bmc1_k_induction                      false
% 2.15/1.00  --bmc1_non_equiv_states                 false
% 2.15/1.00  --bmc1_deadlock                         false
% 2.15/1.00  --bmc1_ucm                              false
% 2.15/1.00  --bmc1_add_unsat_core                   none
% 2.15/1.00  --bmc1_unsat_core_children              false
% 2.15/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/1.00  --bmc1_out_stat                         full
% 2.15/1.00  --bmc1_ground_init                      false
% 2.15/1.00  --bmc1_pre_inst_next_state              false
% 2.15/1.00  --bmc1_pre_inst_state                   false
% 2.15/1.00  --bmc1_pre_inst_reach_state             false
% 2.15/1.00  --bmc1_out_unsat_core                   false
% 2.15/1.00  --bmc1_aig_witness_out                  false
% 2.15/1.00  --bmc1_verbose                          false
% 2.15/1.00  --bmc1_dump_clauses_tptp                false
% 2.15/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.15/1.00  --bmc1_dump_file                        -
% 2.15/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.15/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.15/1.00  --bmc1_ucm_extend_mode                  1
% 2.15/1.00  --bmc1_ucm_init_mode                    2
% 2.15/1.00  --bmc1_ucm_cone_mode                    none
% 2.15/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.15/1.00  --bmc1_ucm_relax_model                  4
% 2.15/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.15/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/1.00  --bmc1_ucm_layered_model                none
% 2.15/1.00  --bmc1_ucm_max_lemma_size               10
% 2.15/1.00  
% 2.15/1.00  ------ AIG Options
% 2.15/1.00  
% 2.15/1.00  --aig_mode                              false
% 2.15/1.00  
% 2.15/1.00  ------ Instantiation Options
% 2.15/1.00  
% 2.15/1.00  --instantiation_flag                    true
% 2.15/1.00  --inst_sos_flag                         false
% 2.15/1.00  --inst_sos_phase                        true
% 2.15/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/1.00  --inst_lit_sel_side                     none
% 2.15/1.00  --inst_solver_per_active                1400
% 2.15/1.00  --inst_solver_calls_frac                1.
% 2.15/1.00  --inst_passive_queue_type               priority_queues
% 2.15/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/1.00  --inst_passive_queues_freq              [25;2]
% 2.15/1.00  --inst_dismatching                      true
% 2.15/1.00  --inst_eager_unprocessed_to_passive     true
% 2.15/1.00  --inst_prop_sim_given                   true
% 2.15/1.00  --inst_prop_sim_new                     false
% 2.15/1.00  --inst_subs_new                         false
% 2.15/1.00  --inst_eq_res_simp                      false
% 2.15/1.00  --inst_subs_given                       false
% 2.15/1.00  --inst_orphan_elimination               true
% 2.15/1.00  --inst_learning_loop_flag               true
% 2.15/1.00  --inst_learning_start                   3000
% 2.15/1.00  --inst_learning_factor                  2
% 2.15/1.00  --inst_start_prop_sim_after_learn       3
% 2.15/1.00  --inst_sel_renew                        solver
% 2.15/1.00  --inst_lit_activity_flag                true
% 2.15/1.00  --inst_restr_to_given                   false
% 2.15/1.00  --inst_activity_threshold               500
% 2.15/1.00  --inst_out_proof                        true
% 2.15/1.00  
% 2.15/1.00  ------ Resolution Options
% 2.15/1.00  
% 2.15/1.00  --resolution_flag                       false
% 2.15/1.00  --res_lit_sel                           adaptive
% 2.15/1.00  --res_lit_sel_side                      none
% 2.15/1.00  --res_ordering                          kbo
% 2.15/1.00  --res_to_prop_solver                    active
% 2.15/1.00  --res_prop_simpl_new                    false
% 2.15/1.00  --res_prop_simpl_given                  true
% 2.15/1.00  --res_passive_queue_type                priority_queues
% 2.15/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/1.00  --res_passive_queues_freq               [15;5]
% 2.15/1.00  --res_forward_subs                      full
% 2.15/1.00  --res_backward_subs                     full
% 2.15/1.00  --res_forward_subs_resolution           true
% 2.15/1.00  --res_backward_subs_resolution          true
% 2.15/1.00  --res_orphan_elimination                true
% 2.15/1.00  --res_time_limit                        2.
% 2.15/1.00  --res_out_proof                         true
% 2.15/1.00  
% 2.15/1.00  ------ Superposition Options
% 2.15/1.00  
% 2.15/1.00  --superposition_flag                    true
% 2.15/1.00  --sup_passive_queue_type                priority_queues
% 2.15/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.15/1.00  --demod_completeness_check              fast
% 2.15/1.00  --demod_use_ground                      true
% 2.15/1.00  --sup_to_prop_solver                    passive
% 2.15/1.00  --sup_prop_simpl_new                    true
% 2.15/1.00  --sup_prop_simpl_given                  true
% 2.15/1.00  --sup_fun_splitting                     false
% 2.15/1.00  --sup_smt_interval                      50000
% 2.15/1.00  
% 2.15/1.00  ------ Superposition Simplification Setup
% 2.15/1.00  
% 2.15/1.00  --sup_indices_passive                   []
% 2.15/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_full_bw                           [BwDemod]
% 2.15/1.00  --sup_immed_triv                        [TrivRules]
% 2.15/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_immed_bw_main                     []
% 2.15/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.00  
% 2.15/1.00  ------ Combination Options
% 2.15/1.00  
% 2.15/1.00  --comb_res_mult                         3
% 2.15/1.00  --comb_sup_mult                         2
% 2.15/1.00  --comb_inst_mult                        10
% 2.15/1.00  
% 2.15/1.00  ------ Debug Options
% 2.15/1.00  
% 2.15/1.00  --dbg_backtrace                         false
% 2.15/1.00  --dbg_dump_prop_clauses                 false
% 2.15/1.00  --dbg_dump_prop_clauses_file            -
% 2.15/1.00  --dbg_out_stat                          false
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  ------ Proving...
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  % SZS status Theorem for theBenchmark.p
% 2.15/1.00  
% 2.15/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.15/1.00  
% 2.15/1.00  fof(f8,axiom,(
% 2.15/1.00    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f22,plain,(
% 2.15/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.15/1.00    inference(ennf_transformation,[],[f8])).
% 2.15/1.00  
% 2.15/1.00  fof(f49,plain,(
% 2.15/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f22])).
% 2.15/1.00  
% 2.15/1.00  fof(f4,axiom,(
% 2.15/1.00    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f16,plain,(
% 2.15/1.00    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 2.15/1.00    inference(ennf_transformation,[],[f4])).
% 2.15/1.00  
% 2.15/1.00  fof(f43,plain,(
% 2.15/1.00    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f16])).
% 2.15/1.00  
% 2.15/1.00  fof(f10,conjecture,(
% 2.15/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f11,negated_conjecture,(
% 2.15/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 2.15/1.00    inference(negated_conjecture,[],[f10])).
% 2.15/1.00  
% 2.15/1.00  fof(f25,plain,(
% 2.15/1.00    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.15/1.00    inference(ennf_transformation,[],[f11])).
% 2.15/1.00  
% 2.15/1.00  fof(f26,plain,(
% 2.15/1.00    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.15/1.00    inference(flattening,[],[f25])).
% 2.15/1.00  
% 2.15/1.00  fof(f36,plain,(
% 2.15/1.00    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 2.15/1.00    introduced(choice_axiom,[])).
% 2.15/1.00  
% 2.15/1.00  fof(f37,plain,(
% 2.15/1.00    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 2.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f36])).
% 2.15/1.00  
% 2.15/1.00  fof(f60,plain,(
% 2.15/1.00    l1_orders_2(sK3)),
% 2.15/1.00    inference(cnf_transformation,[],[f37])).
% 2.15/1.00  
% 2.15/1.00  fof(f3,axiom,(
% 2.15/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f15,plain,(
% 2.15/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.15/1.00    inference(ennf_transformation,[],[f3])).
% 2.15/1.00  
% 2.15/1.00  fof(f42,plain,(
% 2.15/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f15])).
% 2.15/1.00  
% 2.15/1.00  fof(f7,axiom,(
% 2.15/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f20,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.15/1.00    inference(ennf_transformation,[],[f7])).
% 2.15/1.00  
% 2.15/1.00  fof(f21,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.15/1.00    inference(flattening,[],[f20])).
% 2.15/1.00  
% 2.15/1.00  fof(f48,plain,(
% 2.15/1.00    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f21])).
% 2.15/1.00  
% 2.15/1.00  fof(f59,plain,(
% 2.15/1.00    v5_orders_2(sK3)),
% 2.15/1.00    inference(cnf_transformation,[],[f37])).
% 2.15/1.00  
% 2.15/1.00  fof(f56,plain,(
% 2.15/1.00    ~v2_struct_0(sK3)),
% 2.15/1.00    inference(cnf_transformation,[],[f37])).
% 2.15/1.00  
% 2.15/1.00  fof(f57,plain,(
% 2.15/1.00    v3_orders_2(sK3)),
% 2.15/1.00    inference(cnf_transformation,[],[f37])).
% 2.15/1.00  
% 2.15/1.00  fof(f58,plain,(
% 2.15/1.00    v4_orders_2(sK3)),
% 2.15/1.00    inference(cnf_transformation,[],[f37])).
% 2.15/1.00  
% 2.15/1.00  fof(f2,axiom,(
% 2.15/1.00    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f14,plain,(
% 2.15/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.15/1.00    inference(ennf_transformation,[],[f2])).
% 2.15/1.00  
% 2.15/1.00  fof(f27,plain,(
% 2.15/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 2.15/1.00    introduced(choice_axiom,[])).
% 2.15/1.00  
% 2.15/1.00  fof(f28,plain,(
% 2.15/1.00    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 2.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f27])).
% 2.15/1.00  
% 2.15/1.00  fof(f39,plain,(
% 2.15/1.00    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.15/1.00    inference(cnf_transformation,[],[f28])).
% 2.15/1.00  
% 2.15/1.00  fof(f9,axiom,(
% 2.15/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f23,plain,(
% 2.15/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 2.15/1.00    inference(ennf_transformation,[],[f9])).
% 2.15/1.00  
% 2.15/1.00  fof(f24,plain,(
% 2.15/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.15/1.00    inference(flattening,[],[f23])).
% 2.15/1.00  
% 2.15/1.00  fof(f31,plain,(
% 2.15/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.15/1.00    inference(nnf_transformation,[],[f24])).
% 2.15/1.00  
% 2.15/1.00  fof(f32,plain,(
% 2.15/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.15/1.00    inference(rectify,[],[f31])).
% 2.15/1.00  
% 2.15/1.00  fof(f34,plain,(
% 2.15/1.00    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 2.15/1.00    introduced(choice_axiom,[])).
% 2.15/1.00  
% 2.15/1.00  fof(f33,plain,(
% 2.15/1.00    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 2.15/1.00    introduced(choice_axiom,[])).
% 2.15/1.00  
% 2.15/1.00  fof(f35,plain,(
% 2.15/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f34,f33])).
% 2.15/1.00  
% 2.15/1.00  fof(f51,plain,(
% 2.15/1.00    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f35])).
% 2.15/1.00  
% 2.15/1.00  fof(f61,plain,(
% 2.15/1.00    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))),
% 2.15/1.00    inference(cnf_transformation,[],[f37])).
% 2.15/1.00  
% 2.15/1.00  fof(f52,plain,(
% 2.15/1.00    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f35])).
% 2.15/1.00  
% 2.15/1.00  fof(f6,axiom,(
% 2.15/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f19,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.15/1.00    inference(ennf_transformation,[],[f6])).
% 2.15/1.00  
% 2.15/1.00  fof(f29,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.15/1.00    inference(nnf_transformation,[],[f19])).
% 2.15/1.00  
% 2.15/1.00  fof(f30,plain,(
% 2.15/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.15/1.00    inference(flattening,[],[f29])).
% 2.15/1.00  
% 2.15/1.00  fof(f46,plain,(
% 2.15/1.00    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f30])).
% 2.15/1.00  
% 2.15/1.00  fof(f62,plain,(
% 2.15/1.00    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.15/1.00    inference(equality_resolution,[],[f46])).
% 2.15/1.00  
% 2.15/1.00  fof(f50,plain,(
% 2.15/1.00    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f35])).
% 2.15/1.00  
% 2.15/1.00  fof(f1,axiom,(
% 2.15/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f12,plain,(
% 2.15/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.15/1.00    inference(ennf_transformation,[],[f1])).
% 2.15/1.00  
% 2.15/1.00  fof(f13,plain,(
% 2.15/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.15/1.00    inference(flattening,[],[f12])).
% 2.15/1.00  
% 2.15/1.00  fof(f38,plain,(
% 2.15/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f13])).
% 2.15/1.00  
% 2.15/1.00  fof(f5,axiom,(
% 2.15/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f17,plain,(
% 2.15/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.15/1.00    inference(ennf_transformation,[],[f5])).
% 2.15/1.00  
% 2.15/1.00  fof(f18,plain,(
% 2.15/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.15/1.00    inference(flattening,[],[f17])).
% 2.15/1.00  
% 2.15/1.00  fof(f44,plain,(
% 2.15/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f18])).
% 2.15/1.00  
% 2.15/1.00  cnf(c_11,plain,
% 2.15/1.00      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.15/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_5,plain,
% 2.15/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.15/1.00      | ~ l1_struct_0(X0) ),
% 2.15/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_297,plain,
% 2.15/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.15/1.00      | ~ l1_orders_2(X0) ),
% 2.15/1.00      inference(resolution,[status(thm)],[c_11,c_5]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_19,negated_conjecture,
% 2.15/1.00      ( l1_orders_2(sK3) ),
% 2.15/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_664,plain,
% 2.15/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.15/1.00      | sK3 != X0 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_297,c_19]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_665,plain,
% 2.15/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_664]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1149,plain,
% 2.15/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_665]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_4,plain,
% 2.15/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.15/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_308,plain,
% 2.15/1.00      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.15/1.00      inference(resolution,[status(thm)],[c_11,c_4]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_659,plain,
% 2.15/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_308,c_19]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_660,plain,
% 2.15/1.00      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_659]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1165,plain,
% 2.15/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 2.15/1.00      inference(light_normalisation,[status(thm)],[c_1149,c_660]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_10,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | ~ v3_orders_2(X1)
% 2.15/1.00      | ~ v4_orders_2(X1)
% 2.15/1.00      | ~ v5_orders_2(X1)
% 2.15/1.00      | ~ l1_orders_2(X1)
% 2.15/1.00      | v2_struct_0(X1)
% 2.15/1.00      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 2.15/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_20,negated_conjecture,
% 2.15/1.00      ( v5_orders_2(sK3) ),
% 2.15/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_581,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | ~ v3_orders_2(X1)
% 2.15/1.00      | ~ v4_orders_2(X1)
% 2.15/1.00      | ~ l1_orders_2(X1)
% 2.15/1.00      | v2_struct_0(X1)
% 2.15/1.00      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0)
% 2.15/1.00      | sK3 != X1 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_582,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | ~ v3_orders_2(sK3)
% 2.15/1.00      | ~ v4_orders_2(sK3)
% 2.15/1.00      | ~ l1_orders_2(sK3)
% 2.15/1.00      | v2_struct_0(sK3)
% 2.15/1.00      | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_581]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_23,negated_conjecture,
% 2.15/1.00      ( ~ v2_struct_0(sK3) ),
% 2.15/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_22,negated_conjecture,
% 2.15/1.00      ( v3_orders_2(sK3) ),
% 2.15/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_21,negated_conjecture,
% 2.15/1.00      ( v4_orders_2(sK3) ),
% 2.15/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_586,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
% 2.15/1.00      inference(global_propositional_subsumption,
% 2.15/1.00                [status(thm)],
% 2.15/1.00                [c_582,c_23,c_22,c_21,c_19]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1151,plain,
% 2.15/1.00      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 2.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1182,plain,
% 2.15/1.00      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 2.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.15/1.00      inference(light_normalisation,[status(thm)],[c_1151,c_660]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1353,plain,
% 2.15/1.00      ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_1165,c_1182]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_3,plain,
% 2.15/1.00      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.15/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1158,plain,
% 2.15/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_16,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 2.15/1.00      | ~ v3_orders_2(X1)
% 2.15/1.00      | ~ v4_orders_2(X1)
% 2.15/1.00      | ~ v5_orders_2(X1)
% 2.15/1.00      | ~ l1_orders_2(X1)
% 2.15/1.00      | v2_struct_0(X1)
% 2.15/1.00      | sK2(X2,X1,X0) = X2 ),
% 2.15/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_512,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 2.15/1.00      | ~ v3_orders_2(X1)
% 2.15/1.00      | ~ v4_orders_2(X1)
% 2.15/1.00      | ~ l1_orders_2(X1)
% 2.15/1.00      | v2_struct_0(X1)
% 2.15/1.00      | sK2(X2,X1,X0) = X2
% 2.15/1.00      | sK3 != X1 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_513,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
% 2.15/1.00      | ~ v3_orders_2(sK3)
% 2.15/1.00      | ~ v4_orders_2(sK3)
% 2.15/1.00      | ~ l1_orders_2(sK3)
% 2.15/1.00      | v2_struct_0(sK3)
% 2.15/1.00      | sK2(X1,sK3,X0) = X1 ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_512]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_517,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
% 2.15/1.00      | sK2(X1,sK3,X0) = X1 ),
% 2.15/1.00      inference(global_propositional_subsumption,
% 2.15/1.00                [status(thm)],
% 2.15/1.00                [c_513,c_23,c_22,c_21,c_19]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1154,plain,
% 2.15/1.00      ( sK2(X0,sK3,X1) = X0
% 2.15/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.15/1.00      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_517]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1199,plain,
% 2.15/1.00      ( sK2(X0,sK3,X1) = X0
% 2.15/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.15/1.00      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 2.15/1.00      inference(light_normalisation,[status(thm)],[c_1154,c_660]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1516,plain,
% 2.15/1.00      ( sK2(sK0(a_2_1_orders_2(sK3,X0)),sK3,X0) = sK0(a_2_1_orders_2(sK3,X0))
% 2.15/1.00      | a_2_1_orders_2(sK3,X0) = k1_xboole_0
% 2.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_1158,c_1199]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1580,plain,
% 2.15/1.00      ( sK2(sK0(a_2_1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(a_2_1_orders_2(sK3,k2_struct_0(sK3)))
% 2.15/1.00      | a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_1165,c_1516]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1872,plain,
% 2.15/1.00      ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
% 2.15/1.00      | k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 2.15/1.00      inference(demodulation,[status(thm)],[c_1353,c_1580]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_18,negated_conjecture,
% 2.15/1.00      ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.15/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_48,plain,
% 2.15/1.00      ( ~ l1_orders_2(sK3) | l1_struct_0(sK3) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_66,plain,
% 2.15/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | ~ l1_struct_0(sK3) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1298,plain,
% 2.15/1.00      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_586]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1313,plain,
% 2.15/1.00      ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
% 2.15/1.00      | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_897,plain,
% 2.15/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.15/1.00      theory(equality) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1336,plain,
% 2.15/1.00      ( r2_hidden(X0,X1)
% 2.15/1.00      | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
% 2.15/1.00      | X1 != k2_orders_2(sK3,k2_struct_0(sK3))
% 2.15/1.00      | X0 != sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_897]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1483,plain,
% 2.15/1.00      ( r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3)))
% 2.15/1.00      | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
% 2.15/1.00      | X0 != sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
% 2.15/1.00      | a_2_1_orders_2(sK3,k2_struct_0(sK3)) != k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_1336]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1670,plain,
% 2.15/1.00      ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3)))
% 2.15/1.00      | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
% 2.15/1.00      | a_2_1_orders_2(sK3,k2_struct_0(sK3)) != k2_orders_2(sK3,k2_struct_0(sK3))
% 2.15/1.00      | sK0(k2_orders_2(sK3,k2_struct_0(sK3))) != sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_1483]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_895,plain,( X0 = X0 ),theory(equality) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1671,plain,
% 2.15/1.00      ( sK0(k2_orders_2(sK3,k2_struct_0(sK3))) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_895]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1306,plain,
% 2.15/1.00      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3)))
% 2.15/1.00      | sK2(X0,sK3,k2_struct_0(sK3)) = X0 ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_517]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1969,plain,
% 2.15/1.00      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3)))
% 2.15/1.00      | sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
% 2.15/1.00      inference(instantiation,[status(thm)],[c_1306]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2127,plain,
% 2.15/1.00      ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
% 2.15/1.00      inference(global_propositional_subsumption,
% 2.15/1.00                [status(thm)],
% 2.15/1.00                [c_1872,c_19,c_18,c_48,c_66,c_1298,c_1313,c_1670,c_1671,
% 2.15/1.00                 c_1969]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_15,plain,
% 2.15/1.00      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 2.15/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.15/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.15/1.00      | ~ r2_hidden(X3,X2)
% 2.15/1.00      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 2.15/1.00      | ~ v3_orders_2(X0)
% 2.15/1.00      | ~ v4_orders_2(X0)
% 2.15/1.00      | ~ v5_orders_2(X0)
% 2.15/1.00      | ~ l1_orders_2(X0)
% 2.15/1.00      | v2_struct_0(X0) ),
% 2.15/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_440,plain,
% 2.15/1.00      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 2.15/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.15/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.15/1.00      | ~ r2_hidden(X3,X2)
% 2.15/1.00      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 2.15/1.00      | ~ v3_orders_2(X0)
% 2.15/1.00      | ~ v4_orders_2(X0)
% 2.15/1.00      | ~ l1_orders_2(X0)
% 2.15/1.00      | v2_struct_0(X0)
% 2.15/1.00      | sK3 != X0 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_441,plain,
% 2.15/1.00      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
% 2.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.15/1.00      | ~ r2_hidden(X2,X1)
% 2.15/1.00      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
% 2.15/1.00      | ~ v3_orders_2(sK3)
% 2.15/1.00      | ~ v4_orders_2(sK3)
% 2.15/1.00      | ~ l1_orders_2(sK3)
% 2.15/1.00      | v2_struct_0(sK3) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_440]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_445,plain,
% 2.15/1.00      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
% 2.15/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.15/1.00      | ~ r2_hidden(X2,X1)
% 2.15/1.00      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1)) ),
% 2.15/1.00      inference(global_propositional_subsumption,
% 2.15/1.00                [status(thm)],
% 2.15/1.00                [c_441,c_23,c_22,c_21,c_19]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1157,plain,
% 2.15/1.00      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
% 2.15/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.15/1.00      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 2.15/1.00      | r2_hidden(X2,X1) != iProver_top
% 2.15/1.00      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1240,plain,
% 2.15/1.00      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
% 2.15/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.15/1.00      | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
% 2.15/1.00      | r2_hidden(X2,X1) != iProver_top
% 2.15/1.00      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 2.15/1.00      inference(light_normalisation,[status(thm)],[c_1157,c_660]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_8,plain,
% 2.15/1.00      ( ~ r2_orders_2(X0,X1,X1)
% 2.15/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.15/1.00      | ~ l1_orders_2(X0) ),
% 2.15/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_671,plain,
% 2.15/1.00      ( ~ r2_orders_2(X0,X1,X1)
% 2.15/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.15/1.00      | sK3 != X0 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_672,plain,
% 2.15/1.00      ( ~ r2_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_671]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1148,plain,
% 2.15/1.00      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 2.15/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_672]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1177,plain,
% 2.15/1.00      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 2.15/1.00      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 2.15/1.00      inference(light_normalisation,[status(thm)],[c_1148,c_660]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1742,plain,
% 2.15/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.15/1.00      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
% 2.15/1.00      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 2.15/1.00      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_1240,c_1177]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_17,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 2.15/1.00      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 2.15/1.00      | ~ v3_orders_2(X1)
% 2.15/1.00      | ~ v4_orders_2(X1)
% 2.15/1.00      | ~ v5_orders_2(X1)
% 2.15/1.00      | ~ l1_orders_2(X1)
% 2.15/1.00      | v2_struct_0(X1) ),
% 2.15/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_491,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.00      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 2.15/1.00      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 2.15/1.00      | ~ v3_orders_2(X1)
% 2.15/1.00      | ~ v4_orders_2(X1)
% 2.15/1.00      | ~ l1_orders_2(X1)
% 2.15/1.00      | v2_struct_0(X1)
% 2.15/1.00      | sK3 != X1 ),
% 2.15/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_492,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 2.15/1.00      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
% 2.15/1.00      | ~ v3_orders_2(sK3)
% 2.15/1.00      | ~ v4_orders_2(sK3)
% 2.15/1.00      | ~ l1_orders_2(sK3)
% 2.15/1.00      | v2_struct_0(sK3) ),
% 2.15/1.00      inference(unflattening,[status(thm)],[c_491]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_496,plain,
% 2.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.00      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 2.15/1.00      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0)) ),
% 2.15/1.00      inference(global_propositional_subsumption,
% 2.15/1.00                [status(thm)],
% 2.15/1.00                [c_492,c_23,c_22,c_21,c_19]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1155,plain,
% 2.15/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.15/1.00      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) = iProver_top
% 2.15/1.00      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
% 2.15/1.00      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1206,plain,
% 2.15/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.15/1.00      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 2.15/1.00      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
% 2.15/1.01      inference(light_normalisation,[status(thm)],[c_1155,c_660]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2008,plain,
% 2.15/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.15/1.01      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 2.15/1.01      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 2.15/1.01      inference(global_propositional_subsumption,
% 2.15/1.01                [status(thm)],
% 2.15/1.01                [c_1742,c_1206]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2131,plain,
% 2.15/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.15/1.01      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.15/1.01      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
% 2.15/1.01      inference(superposition,[status(thm)],[c_2127,c_2008]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2151,plain,
% 2.15/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.15/1.01      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.15/1.01      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
% 2.15/1.01      inference(light_normalisation,[status(thm)],[c_2131,c_1353]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_0,plain,
% 2.15/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.15/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_6,plain,
% 2.15/1.01      ( v2_struct_0(X0)
% 2.15/1.01      | ~ l1_struct_0(X0)
% 2.15/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.15/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_283,plain,
% 2.15/1.01      ( ~ l1_orders_2(X0)
% 2.15/1.01      | v2_struct_0(X0)
% 2.15/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.15/1.01      inference(resolution,[status(thm)],[c_11,c_6]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_631,plain,
% 2.15/1.01      ( ~ l1_orders_2(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 2.15/1.01      inference(resolution_lifted,[status(thm)],[c_283,c_23]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_632,plain,
% 2.15/1.01      ( ~ l1_orders_2(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.15/1.01      inference(unflattening,[status(thm)],[c_631]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_63,plain,
% 2.15/1.01      ( v2_struct_0(sK3)
% 2.15/1.01      | ~ l1_struct_0(sK3)
% 2.15/1.01      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.15/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_634,plain,
% 2.15/1.01      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.15/1.01      inference(global_propositional_subsumption,
% 2.15/1.01                [status(thm)],
% 2.15/1.01                [c_632,c_23,c_19,c_48,c_63]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_644,plain,
% 2.15/1.01      ( ~ m1_subset_1(X0,X1)
% 2.15/1.01      | r2_hidden(X0,X1)
% 2.15/1.01      | u1_struct_0(sK3) != X1 ),
% 2.15/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_634]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_645,plain,
% 2.15/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.15/1.01      | r2_hidden(X0,u1_struct_0(sK3)) ),
% 2.15/1.01      inference(unflattening,[status(thm)],[c_644]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1150,plain,
% 2.15/1.01      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.15/1.01      | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top ),
% 2.15/1.01      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1172,plain,
% 2.15/1.01      ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 2.15/1.01      | r2_hidden(X0,k2_struct_0(sK3)) = iProver_top ),
% 2.15/1.01      inference(light_normalisation,[status(thm)],[c_1150,c_660]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1441,plain,
% 2.15/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.15/1.01      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 2.15/1.01      | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top ),
% 2.15/1.01      inference(superposition,[status(thm)],[c_1206,c_1172]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2132,plain,
% 2.15/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.15/1.01      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.15/1.01      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
% 2.15/1.01      inference(superposition,[status(thm)],[c_2127,c_1441]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2144,plain,
% 2.15/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.15/1.01      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.15/1.01      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
% 2.15/1.01      inference(light_normalisation,[status(thm)],[c_2132,c_1353]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_2155,plain,
% 2.15/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.15/1.01      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 2.15/1.01      inference(backward_subsumption_resolution,
% 2.15/1.01                [status(thm)],
% 2.15/1.01                [c_2151,c_2144]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(c_1314,plain,
% 2.15/1.01      ( k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3))
% 2.15/1.01      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) = iProver_top ),
% 2.15/1.01      inference(predicate_to_equality,[status(thm)],[c_1313]) ).
% 2.15/1.01  
% 2.15/1.01  cnf(contradiction,plain,
% 2.15/1.01      ( $false ),
% 2.15/1.01      inference(minisat,[status(thm)],[c_2155,c_1314,c_1165,c_18]) ).
% 2.15/1.01  
% 2.15/1.01  
% 2.15/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.15/1.01  
% 2.15/1.01  ------                               Statistics
% 2.15/1.01  
% 2.15/1.01  ------ General
% 2.15/1.01  
% 2.15/1.01  abstr_ref_over_cycles:                  0
% 2.15/1.01  abstr_ref_under_cycles:                 0
% 2.15/1.01  gc_basic_clause_elim:                   0
% 2.15/1.01  forced_gc_time:                         0
% 2.15/1.01  parsing_time:                           0.009
% 2.15/1.01  unif_index_cands_time:                  0.
% 2.15/1.01  unif_index_add_time:                    0.
% 2.15/1.01  orderings_time:                         0.
% 2.15/1.01  out_proof_time:                         0.014
% 2.15/1.01  total_time:                             0.14
% 2.15/1.01  num_of_symbols:                         53
% 2.15/1.01  num_of_terms:                           1768
% 2.15/1.01  
% 2.15/1.01  ------ Preprocessing
% 2.15/1.01  
% 2.15/1.01  num_of_splits:                          0
% 2.15/1.01  num_of_split_atoms:                     0
% 2.15/1.01  num_of_reused_defs:                     0
% 2.15/1.01  num_eq_ax_congr_red:                    39
% 2.15/1.01  num_of_sem_filtered_clauses:            1
% 2.15/1.01  num_of_subtypes:                        0
% 2.15/1.01  monotx_restored_types:                  0
% 2.15/1.01  sat_num_of_epr_types:                   0
% 2.15/1.01  sat_num_of_non_cyclic_types:            0
% 2.15/1.01  sat_guarded_non_collapsed_types:        0
% 2.15/1.01  num_pure_diseq_elim:                    0
% 2.15/1.01  simp_replaced_by:                       0
% 2.15/1.01  res_preprocessed:                       94
% 2.15/1.01  prep_upred:                             0
% 2.15/1.01  prep_unflattend:                        28
% 2.15/1.01  smt_new_axioms:                         0
% 2.15/1.01  pred_elim_cands:                        3
% 2.15/1.01  pred_elim:                              8
% 2.15/1.01  pred_elim_cl:                           9
% 2.15/1.01  pred_elim_cycles:                       13
% 2.15/1.01  merged_defs:                            0
% 2.15/1.01  merged_defs_ncl:                        0
% 2.15/1.01  bin_hyper_res:                          0
% 2.15/1.01  prep_cycles:                            4
% 2.15/1.01  pred_elim_time:                         0.018
% 2.15/1.01  splitting_time:                         0.
% 2.15/1.01  sem_filter_time:                        0.
% 2.15/1.01  monotx_time:                            0.001
% 2.15/1.01  subtype_inf_time:                       0.
% 2.15/1.01  
% 2.15/1.01  ------ Problem properties
% 2.15/1.01  
% 2.15/1.01  clauses:                                15
% 2.15/1.01  conjectures:                            1
% 2.15/1.01  epr:                                    0
% 2.15/1.01  horn:                                   12
% 2.15/1.01  ground:                                 3
% 2.15/1.01  unary:                                  3
% 2.15/1.01  binary:                                 4
% 2.15/1.01  lits:                                   40
% 2.15/1.01  lits_eq:                                9
% 2.15/1.01  fd_pure:                                0
% 2.15/1.01  fd_pseudo:                              0
% 2.15/1.01  fd_cond:                                3
% 2.15/1.01  fd_pseudo_cond:                         0
% 2.15/1.01  ac_symbols:                             0
% 2.15/1.01  
% 2.15/1.01  ------ Propositional Solver
% 2.15/1.01  
% 2.15/1.01  prop_solver_calls:                      26
% 2.15/1.01  prop_fast_solver_calls:                 807
% 2.15/1.01  smt_solver_calls:                       0
% 2.15/1.01  smt_fast_solver_calls:                  0
% 2.15/1.01  prop_num_of_clauses:                    641
% 2.15/1.01  prop_preprocess_simplified:             3039
% 2.15/1.01  prop_fo_subsumed:                       37
% 2.15/1.01  prop_solver_time:                       0.
% 2.15/1.01  smt_solver_time:                        0.
% 2.15/1.01  smt_fast_solver_time:                   0.
% 2.15/1.01  prop_fast_solver_time:                  0.
% 2.15/1.01  prop_unsat_core_time:                   0.
% 2.15/1.01  
% 2.15/1.01  ------ QBF
% 2.15/1.01  
% 2.15/1.01  qbf_q_res:                              0
% 2.15/1.01  qbf_num_tautologies:                    0
% 2.15/1.01  qbf_prep_cycles:                        0
% 2.15/1.01  
% 2.15/1.01  ------ BMC1
% 2.15/1.01  
% 2.15/1.01  bmc1_current_bound:                     -1
% 2.15/1.01  bmc1_last_solved_bound:                 -1
% 2.15/1.01  bmc1_unsat_core_size:                   -1
% 2.15/1.01  bmc1_unsat_core_parents_size:           -1
% 2.15/1.01  bmc1_merge_next_fun:                    0
% 2.15/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.15/1.01  
% 2.15/1.01  ------ Instantiation
% 2.15/1.01  
% 2.15/1.01  inst_num_of_clauses:                    167
% 2.15/1.01  inst_num_in_passive:                    8
% 2.15/1.01  inst_num_in_active:                     109
% 2.15/1.01  inst_num_in_unprocessed:                50
% 2.15/1.01  inst_num_of_loops:                      120
% 2.15/1.01  inst_num_of_learning_restarts:          0
% 2.15/1.01  inst_num_moves_active_passive:          8
% 2.15/1.01  inst_lit_activity:                      0
% 2.15/1.01  inst_lit_activity_moves:                0
% 2.15/1.01  inst_num_tautologies:                   0
% 2.15/1.01  inst_num_prop_implied:                  0
% 2.15/1.01  inst_num_existing_simplified:           0
% 2.15/1.01  inst_num_eq_res_simplified:             0
% 2.15/1.01  inst_num_child_elim:                    0
% 2.15/1.01  inst_num_of_dismatching_blockings:      20
% 2.15/1.01  inst_num_of_non_proper_insts:           140
% 2.15/1.01  inst_num_of_duplicates:                 0
% 2.15/1.01  inst_inst_num_from_inst_to_res:         0
% 2.15/1.01  inst_dismatching_checking_time:         0.
% 2.15/1.01  
% 2.15/1.01  ------ Resolution
% 2.15/1.01  
% 2.15/1.01  res_num_of_clauses:                     0
% 2.15/1.01  res_num_in_passive:                     0
% 2.15/1.01  res_num_in_active:                      0
% 2.15/1.01  res_num_of_loops:                       98
% 2.15/1.01  res_forward_subset_subsumed:            32
% 2.15/1.01  res_backward_subset_subsumed:           0
% 2.15/1.01  res_forward_subsumed:                   0
% 2.15/1.01  res_backward_subsumed:                  0
% 2.15/1.01  res_forward_subsumption_resolution:     3
% 2.15/1.01  res_backward_subsumption_resolution:    0
% 2.15/1.01  res_clause_to_clause_subsumption:       81
% 2.15/1.01  res_orphan_elimination:                 0
% 2.15/1.01  res_tautology_del:                      20
% 2.15/1.01  res_num_eq_res_simplified:              0
% 2.15/1.01  res_num_sel_changes:                    0
% 2.15/1.01  res_moves_from_active_to_pass:          0
% 2.15/1.01  
% 2.15/1.01  ------ Superposition
% 2.15/1.01  
% 2.15/1.01  sup_time_total:                         0.
% 2.15/1.01  sup_time_generating:                    0.
% 2.15/1.01  sup_time_sim_full:                      0.
% 2.15/1.01  sup_time_sim_immed:                     0.
% 2.15/1.01  
% 2.15/1.01  sup_num_of_clauses:                     30
% 2.15/1.01  sup_num_in_active:                      23
% 2.15/1.01  sup_num_in_passive:                     7
% 2.15/1.01  sup_num_of_loops:                       23
% 2.15/1.01  sup_fw_superposition:                   6
% 2.15/1.01  sup_bw_superposition:                   13
% 2.15/1.01  sup_immediate_simplified:               8
% 2.15/1.01  sup_given_eliminated:                   0
% 2.15/1.01  comparisons_done:                       0
% 2.15/1.01  comparisons_avoided:                    6
% 2.15/1.01  
% 2.15/1.01  ------ Simplifications
% 2.15/1.01  
% 2.15/1.01  
% 2.15/1.01  sim_fw_subset_subsumed:                 0
% 2.15/1.01  sim_bw_subset_subsumed:                 1
% 2.15/1.01  sim_fw_subsumed:                        0
% 2.15/1.01  sim_bw_subsumed:                        1
% 2.15/1.01  sim_fw_subsumption_res:                 0
% 2.15/1.01  sim_bw_subsumption_res:                 1
% 2.15/1.01  sim_tautology_del:                      0
% 2.15/1.01  sim_eq_tautology_del:                   0
% 2.15/1.01  sim_eq_res_simp:                        0
% 2.15/1.01  sim_fw_demodulated:                     1
% 2.15/1.01  sim_bw_demodulated:                     1
% 2.15/1.01  sim_light_normalised:                   16
% 2.15/1.01  sim_joinable_taut:                      0
% 2.15/1.01  sim_joinable_simp:                      0
% 2.15/1.01  sim_ac_normalised:                      0
% 2.15/1.01  sim_smt_subsumption:                    0
% 2.15/1.01  
%------------------------------------------------------------------------------
