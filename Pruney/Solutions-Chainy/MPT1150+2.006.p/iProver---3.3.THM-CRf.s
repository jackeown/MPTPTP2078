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
% DateTime   : Thu Dec  3 12:12:05 EST 2020

% Result     : Theorem 11.84s
% Output     : CNFRefutation 11.84s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 703 expanded)
%              Number of clauses        :  123 ( 248 expanded)
%              Number of leaves         :   24 ( 140 expanded)
%              Depth                    :   22
%              Number of atoms          :  726 (3078 expanded)
%              Number of equality atoms :  266 ( 730 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f33])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f31,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f45])).

fof(f75,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
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
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
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
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X4,X3)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X6,X5)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f40])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X6,X5)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,X6,sK2(X0,X1,X2))
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
                & r2_hidden(sK1(X1,X2,X3),X2)
                & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,X6,sK2(X0,X1,X2))
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK2(X0,X1,X2) = X0
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f43,f42])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f67,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X1,X6,sK2(X0,X1,X2))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
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

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_539,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3695,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(X2),X3)
    | X1 != X3
    | X0 != sK0(X2) ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_8255,plain,
    ( ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),X0)
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),X1)
    | X1 != X0
    | sK0(k1_orders_2(sK3,k2_struct_0(sK3))) != sK0(k1_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3695])).

cnf(c_20390,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),X0)
    | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),u1_struct_0(sK3))
    | X0 != u1_struct_0(sK3)
    | sK0(k1_orders_2(sK3,k2_struct_0(sK3))) != sK0(k1_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_8255])).

cnf(c_23786,plain,
    ( ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),u1_struct_0(sK3))
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3))
    | k2_struct_0(sK3) != u1_struct_0(sK3)
    | sK0(k1_orders_2(sK3,k2_struct_0(sK3))) != sK0(k1_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_20390])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1259,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1257,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1254,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_25,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1237,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_17,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1244,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1855,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1244])).

cnf(c_11,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1250,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1982,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_1855,c_1250])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1246,plain,
    ( a_2_0_orders_2(X0,X1) = k1_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3864,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1982,c_1246])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_31,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,plain,
    ( v4_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_33,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_34,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4193,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3864,c_30,c_31,c_32,c_33,c_34])).

cnf(c_4194,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4193])).

cnf(c_4201,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | r1_tarski(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_4194])).

cnf(c_4562,plain,
    ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1257,c_4201])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1239,plain,
    ( sK2(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(X1,X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2459,plain,
    ( sK2(X0,sK3,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1982,c_1239])).

cnf(c_3013,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | sK2(X0,sK3,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2459,c_30,c_31,c_32,c_33,c_34])).

cnf(c_3014,plain,
    ( sK2(X0,sK3,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3013])).

cnf(c_5096,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4562,c_3014])).

cnf(c_4117,plain,
    ( r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4120,plain,
    ( r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4117])).

cnf(c_4122,plain,
    ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4120])).

cnf(c_2806,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(X0))
    | ~ r1_tarski(k2_struct_0(sK3),X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5083,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3)))
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2806])).

cnf(c_5087,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5083])).

cnf(c_5794,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5096,c_4122,c_5087])).

cnf(c_5802,plain,
    ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)))
    | k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1259,c_5794])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1574,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
    | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1679,plain,
    ( ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),sK0(k1_orders_2(sK3,k2_struct_0(sK3))))
    | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_540,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1811,plain,
    ( ~ r1_tarski(X0,sK0(k1_orders_2(sK3,k2_struct_0(sK3))))
    | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),sK0(k1_orders_2(sK3,k2_struct_0(sK3))))
    | k1_orders_2(sK3,k2_struct_0(sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_1968,plain,
    ( r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),sK0(k1_orders_2(sK3,k2_struct_0(sK3))))
    | ~ r1_tarski(k1_xboole_0,sK0(k1_orders_2(sK3,k2_struct_0(sK3))))
    | k1_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1811])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1969,plain,
    ( r1_tarski(k1_xboole_0,sK0(k1_orders_2(sK3,k2_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_13293,plain,
    ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5802,c_24,c_1574,c_1679,c_1968,c_1969])).

cnf(c_21,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1240,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1252,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1472,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1240,c_1252])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1238,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1)) = iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X1,X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2093,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1982,c_1238])).

cnf(c_2094,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2093,c_1982])).

cnf(c_2099,plain,
    ( r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2094,c_30,c_31,c_32,c_33,c_34])).

cnf(c_2100,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2099])).

cnf(c_13,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1248,plain,
    ( r2_orders_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2860,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1982,c_1248])).

cnf(c_2890,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | r2_orders_2(sK3,X0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2860,c_34])).

cnf(c_2891,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2890])).

cnf(c_2898,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),sK2(X0,sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2891])).

cnf(c_6467,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1472,c_2898])).

cnf(c_6477,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6467,c_1982])).

cnf(c_7283,plain,
    ( r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6477,c_30,c_31,c_32,c_33,c_34])).

cnf(c_7284,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7283])).

cnf(c_13303,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13293,c_7284])).

cnf(c_13362,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13303,c_4562])).

cnf(c_13447,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3)))
    | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
    | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13362])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_197,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_198,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_197])).

cnf(c_261,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_198])).

cnf(c_1664,plain,
    ( ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X0)
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),X0)
    | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_12501,plain,
    ( ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1664])).

cnf(c_1827,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X1)
    | k1_orders_2(sK3,k2_struct_0(sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_4669,plain,
    ( ~ r1_tarski(k1_orders_2(X0,u1_struct_0(sK3)),X1)
    | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X1)
    | k1_orders_2(sK3,k2_struct_0(sK3)) != k1_orders_2(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1827])).

cnf(c_10124,plain,
    ( ~ r1_tarski(k1_orders_2(sK3,u1_struct_0(sK3)),u1_struct_0(sK3))
    | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),u1_struct_0(sK3))
    | k1_orders_2(sK3,k2_struct_0(sK3)) != k1_orders_2(sK3,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4669])).

cnf(c_546,plain,
    ( X0 != X1
    | X2 != X3
    | k1_orders_2(X0,X2) = k1_orders_2(X1,X3) ),
    theory(equality)).

cnf(c_1698,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(X0,X1)
    | k2_struct_0(sK3) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_4347,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(X0,u1_struct_0(sK3))
    | k2_struct_0(sK3) != u1_struct_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1698])).

cnf(c_4348,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,u1_struct_0(sK3))
    | k2_struct_0(sK3) != u1_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4347])).

cnf(c_4121,plain,
    ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4117])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1789,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3474,plain,
    ( ~ m1_subset_1(k1_orders_2(X0,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
    | r1_tarski(k1_orders_2(X0,u1_struct_0(X0)),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1789])).

cnf(c_3486,plain,
    ( ~ m1_subset_1(k1_orders_2(sK3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(k1_orders_2(sK3,u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3474])).

cnf(c_538,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_1948,plain,
    ( X0 != X1
    | k2_struct_0(sK3) != X1
    | k2_struct_0(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_2418,plain,
    ( X0 != k2_struct_0(sK3)
    | k2_struct_0(sK3) = X0
    | k2_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1948])).

cnf(c_2824,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | k2_struct_0(sK3) = u1_struct_0(sK3)
    | k2_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2418])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2168,plain,
    ( m1_subset_1(k1_orders_2(X0,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2170,plain,
    ( m1_subset_1(k1_orders_2(sK3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_2168])).

cnf(c_537,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1920,plain,
    ( sK0(k1_orders_2(sK3,k2_struct_0(sK3))) = sK0(k1_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_1795,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1801,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1795])).

cnf(c_1606,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1794,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1606])).

cnf(c_1797,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1794])).

cnf(c_543,plain,
    ( X0 != X1
    | k2_struct_0(X0) = k2_struct_0(X1) ),
    theory(equality)).

cnf(c_555,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_98,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_94,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_72,plain,
    ( ~ l1_struct_0(sK3)
    | u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_54,plain,
    ( ~ l1_orders_2(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23786,c_13447,c_12501,c_10124,c_5083,c_4348,c_4121,c_3486,c_2824,c_2170,c_1920,c_1801,c_1797,c_1574,c_555,c_98,c_94,c_72,c_54,c_24,c_25,c_26,c_27,c_28,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:12:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 11.84/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.84/2.00  
% 11.84/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.84/2.00  
% 11.84/2.00  ------  iProver source info
% 11.84/2.00  
% 11.84/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.84/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.84/2.00  git: non_committed_changes: false
% 11.84/2.00  git: last_make_outside_of_git: false
% 11.84/2.00  
% 11.84/2.00  ------ 
% 11.84/2.00  ------ Parsing...
% 11.84/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.84/2.00  
% 11.84/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.84/2.00  
% 11.84/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.84/2.00  
% 11.84/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.84/2.00  ------ Proving...
% 11.84/2.00  ------ Problem Properties 
% 11.84/2.00  
% 11.84/2.00  
% 11.84/2.00  clauses                                 29
% 11.84/2.00  conjectures                             6
% 11.84/2.00  EPR                                     11
% 11.84/2.00  Horn                                    19
% 11.84/2.00  unary                                   9
% 11.84/2.00  binary                                  6
% 11.84/2.00  lits                                    111
% 11.84/2.00  lits eq                                 7
% 11.84/2.00  fd_pure                                 0
% 11.84/2.00  fd_pseudo                               0
% 11.84/2.00  fd_cond                                 1
% 11.84/2.00  fd_pseudo_cond                          2
% 11.84/2.00  AC symbols                              0
% 11.84/2.00  
% 11.84/2.00  ------ Input Options Time Limit: Unbounded
% 11.84/2.00  
% 11.84/2.00  
% 11.84/2.00  ------ 
% 11.84/2.00  Current options:
% 11.84/2.00  ------ 
% 11.84/2.00  
% 11.84/2.00  
% 11.84/2.00  
% 11.84/2.00  
% 11.84/2.00  ------ Proving...
% 11.84/2.00  
% 11.84/2.00  
% 11.84/2.00  % SZS status Theorem for theBenchmark.p
% 11.84/2.00  
% 11.84/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.84/2.00  
% 11.84/2.00  fof(f1,axiom,(
% 11.84/2.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 11.84/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.84/2.00  
% 11.84/2.00  fof(f17,plain,(
% 11.84/2.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 11.84/2.00    inference(ennf_transformation,[],[f1])).
% 11.84/2.00  
% 11.84/2.00  fof(f33,plain,(
% 11.84/2.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 11.84/2.00    introduced(choice_axiom,[])).
% 11.84/2.00  
% 11.84/2.00  fof(f34,plain,(
% 11.84/2.00    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 11.84/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f33])).
% 11.84/2.00  
% 11.84/2.00  fof(f47,plain,(
% 11.84/2.00    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 11.84/2.00    inference(cnf_transformation,[],[f34])).
% 11.84/2.00  
% 11.84/2.00  fof(f2,axiom,(
% 11.84/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.84/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.84/2.00  
% 11.84/2.00  fof(f35,plain,(
% 11.84/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.84/2.00    inference(nnf_transformation,[],[f2])).
% 11.84/2.00  
% 11.84/2.00  fof(f36,plain,(
% 11.84/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.84/2.00    inference(flattening,[],[f35])).
% 11.84/2.00  
% 11.84/2.00  fof(f48,plain,(
% 11.84/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.84/2.00    inference(cnf_transformation,[],[f36])).
% 11.84/2.00  
% 11.84/2.00  fof(f78,plain,(
% 11.84/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.84/2.00    inference(equality_resolution,[],[f48])).
% 11.84/2.00  
% 11.84/2.00  fof(f6,axiom,(
% 11.84/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.84/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.84/2.00  
% 11.84/2.00  fof(f37,plain,(
% 11.84/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.84/2.00    inference(nnf_transformation,[],[f6])).
% 11.84/2.00  
% 11.84/2.00  fof(f55,plain,(
% 11.84/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.84/2.00    inference(cnf_transformation,[],[f37])).
% 11.84/2.00  
% 11.84/2.00  fof(f15,conjecture,(
% 11.84/2.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 11.84/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.84/2.00  
% 11.84/2.00  fof(f16,negated_conjecture,(
% 11.84/2.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 11.84/2.00    inference(negated_conjecture,[],[f15])).
% 11.84/2.00  
% 11.84/2.00  fof(f31,plain,(
% 11.84/2.00    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 11.84/2.00    inference(ennf_transformation,[],[f16])).
% 11.84/2.00  
% 11.84/2.00  fof(f32,plain,(
% 11.84/2.00    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.84/2.00    inference(flattening,[],[f31])).
% 11.84/2.00  
% 11.84/2.00  fof(f45,plain,(
% 11.84/2.00    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 11.84/2.00    introduced(choice_axiom,[])).
% 11.84/2.00  
% 11.84/2.00  fof(f46,plain,(
% 11.84/2.00    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 11.84/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f45])).
% 11.84/2.00  
% 11.84/2.00  fof(f75,plain,(
% 11.84/2.00    l1_orders_2(sK3)),
% 11.84/2.00    inference(cnf_transformation,[],[f46])).
% 11.84/2.00  
% 11.84/2.00  fof(f13,axiom,(
% 11.84/2.00    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 11.84/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.84/2.00  
% 11.84/2.00  fof(f28,plain,(
% 11.84/2.00    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 11.84/2.00    inference(ennf_transformation,[],[f13])).
% 11.84/2.00  
% 11.84/2.00  fof(f64,plain,(
% 11.84/2.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 11.84/2.00    inference(cnf_transformation,[],[f28])).
% 11.84/2.00  
% 11.84/2.00  fof(f9,axiom,(
% 11.84/2.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 11.84/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.84/2.00  
% 11.84/2.00  fof(f22,plain,(
% 11.84/2.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 11.84/2.00    inference(ennf_transformation,[],[f9])).
% 11.84/2.00  
% 11.84/2.00  fof(f58,plain,(
% 11.84/2.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 11.84/2.00    inference(cnf_transformation,[],[f22])).
% 11.84/2.00  
% 11.84/2.00  fof(f11,axiom,(
% 11.84/2.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 11.84/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.84/2.00  
% 11.84/2.00  fof(f24,plain,(
% 11.84/2.00    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 11.84/2.00    inference(ennf_transformation,[],[f11])).
% 11.84/2.00  
% 11.84/2.00  fof(f25,plain,(
% 11.84/2.00    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 11.84/2.00    inference(flattening,[],[f24])).
% 11.84/2.00  
% 11.84/2.00  fof(f62,plain,(
% 11.84/2.00    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 11.84/2.00    inference(cnf_transformation,[],[f25])).
% 11.84/2.00  
% 11.84/2.00  fof(f71,plain,(
% 11.84/2.00    ~v2_struct_0(sK3)),
% 11.84/2.00    inference(cnf_transformation,[],[f46])).
% 11.84/2.00  
% 11.84/2.00  fof(f72,plain,(
% 11.84/2.00    v3_orders_2(sK3)),
% 11.84/2.00    inference(cnf_transformation,[],[f46])).
% 11.84/2.00  
% 11.84/2.00  fof(f73,plain,(
% 11.84/2.00    v4_orders_2(sK3)),
% 11.84/2.00    inference(cnf_transformation,[],[f46])).
% 11.84/2.00  
% 11.84/2.00  fof(f74,plain,(
% 11.84/2.00    v5_orders_2(sK3)),
% 11.84/2.00    inference(cnf_transformation,[],[f46])).
% 11.84/2.00  
% 11.84/2.00  fof(f14,axiom,(
% 11.84/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 11.84/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.84/2.00  
% 11.84/2.00  fof(f29,plain,(
% 11.84/2.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 11.84/2.00    inference(ennf_transformation,[],[f14])).
% 11.84/2.00  
% 11.84/2.00  fof(f30,plain,(
% 11.84/2.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 11.84/2.00    inference(flattening,[],[f29])).
% 11.84/2.00  
% 11.84/2.00  fof(f40,plain,(
% 11.84/2.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 11.84/2.00    inference(nnf_transformation,[],[f30])).
% 11.84/2.00  
% 11.84/2.00  fof(f41,plain,(
% 11.84/2.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 11.84/2.00    inference(rectify,[],[f40])).
% 11.84/2.00  
% 11.84/2.00  fof(f43,plain,(
% 11.84/2.00    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 11.84/2.00    introduced(choice_axiom,[])).
% 11.84/2.00  
% 11.84/2.00  fof(f42,plain,(
% 11.84/2.00    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 11.84/2.00    introduced(choice_axiom,[])).
% 11.84/2.00  
% 11.84/2.00  fof(f44,plain,(
% 11.84/2.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 11.84/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f43,f42])).
% 11.84/2.00  
% 11.84/2.00  fof(f66,plain,(
% 11.84/2.00    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 11.84/2.00    inference(cnf_transformation,[],[f44])).
% 11.84/2.00  
% 11.84/2.00  fof(f76,plain,(
% 11.84/2.00    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))),
% 11.84/2.00    inference(cnf_transformation,[],[f46])).
% 11.84/2.00  
% 11.84/2.00  fof(f8,axiom,(
% 11.84/2.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 11.84/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.84/2.00  
% 11.84/2.00  fof(f21,plain,(
% 11.84/2.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 11.84/2.00    inference(ennf_transformation,[],[f8])).
% 11.84/2.00  
% 11.84/2.00  fof(f57,plain,(
% 11.84/2.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 11.84/2.00    inference(cnf_transformation,[],[f21])).
% 11.84/2.00  
% 11.84/2.00  fof(f3,axiom,(
% 11.84/2.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.84/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.84/2.00  
% 11.84/2.00  fof(f51,plain,(
% 11.84/2.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.84/2.00    inference(cnf_transformation,[],[f3])).
% 11.84/2.00  
% 11.84/2.00  fof(f67,plain,(
% 11.84/2.00    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 11.84/2.00    inference(cnf_transformation,[],[f44])).
% 11.84/2.00  
% 11.84/2.00  fof(f7,axiom,(
% 11.84/2.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 11.84/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.84/2.00  
% 11.84/2.00  fof(f19,plain,(
% 11.84/2.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 11.84/2.00    inference(ennf_transformation,[],[f7])).
% 11.84/2.00  
% 11.84/2.00  fof(f20,plain,(
% 11.84/2.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.84/2.00    inference(flattening,[],[f19])).
% 11.84/2.00  
% 11.84/2.00  fof(f56,plain,(
% 11.84/2.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.84/2.00    inference(cnf_transformation,[],[f20])).
% 11.84/2.00  
% 11.84/2.00  fof(f65,plain,(
% 11.84/2.00    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 11.84/2.00    inference(cnf_transformation,[],[f44])).
% 11.84/2.00  
% 11.84/2.00  fof(f10,axiom,(
% 11.84/2.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 11.84/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.84/2.00  
% 11.84/2.00  fof(f23,plain,(
% 11.84/2.00    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.84/2.00    inference(ennf_transformation,[],[f10])).
% 11.84/2.00  
% 11.84/2.00  fof(f38,plain,(
% 11.84/2.00    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.84/2.00    inference(nnf_transformation,[],[f23])).
% 11.84/2.00  
% 11.84/2.00  fof(f39,plain,(
% 11.84/2.00    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.84/2.00    inference(flattening,[],[f38])).
% 11.84/2.00  
% 11.84/2.00  fof(f60,plain,(
% 11.84/2.00    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.84/2.00    inference(cnf_transformation,[],[f39])).
% 11.84/2.00  
% 11.84/2.00  fof(f79,plain,(
% 11.84/2.00    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.84/2.00    inference(equality_resolution,[],[f60])).
% 11.84/2.00  
% 11.84/2.00  fof(f4,axiom,(
% 11.84/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 11.84/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.84/2.00  
% 11.84/2.00  fof(f18,plain,(
% 11.84/2.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.84/2.00    inference(ennf_transformation,[],[f4])).
% 11.84/2.00  
% 11.84/2.00  fof(f52,plain,(
% 11.84/2.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.84/2.00    inference(cnf_transformation,[],[f18])).
% 11.84/2.00  
% 11.84/2.00  fof(f54,plain,(
% 11.84/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.84/2.00    inference(cnf_transformation,[],[f37])).
% 11.84/2.00  
% 11.84/2.00  fof(f12,axiom,(
% 11.84/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.84/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.84/2.00  
% 11.84/2.00  fof(f26,plain,(
% 11.84/2.00    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 11.84/2.00    inference(ennf_transformation,[],[f12])).
% 11.84/2.00  
% 11.84/2.00  fof(f27,plain,(
% 11.84/2.00    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 11.84/2.00    inference(flattening,[],[f26])).
% 11.84/2.00  
% 11.84/2.00  fof(f63,plain,(
% 11.84/2.00    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 11.84/2.00    inference(cnf_transformation,[],[f27])).
% 11.84/2.00  
% 11.84/2.00  fof(f50,plain,(
% 11.84/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.84/2.00    inference(cnf_transformation,[],[f36])).
% 11.84/2.00  
% 11.84/2.00  cnf(c_539,plain,
% 11.84/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.84/2.00      theory(equality) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_3695,plain,
% 11.84/2.00      ( r2_hidden(X0,X1)
% 11.84/2.00      | ~ r2_hidden(sK0(X2),X3)
% 11.84/2.00      | X1 != X3
% 11.84/2.00      | X0 != sK0(X2) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_539]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_8255,plain,
% 11.84/2.00      ( ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),X0)
% 11.84/2.00      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),X1)
% 11.84/2.00      | X1 != X0
% 11.84/2.00      | sK0(k1_orders_2(sK3,k2_struct_0(sK3))) != sK0(k1_orders_2(sK3,k2_struct_0(sK3))) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_3695]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_20390,plain,
% 11.84/2.00      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),X0)
% 11.84/2.00      | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),u1_struct_0(sK3))
% 11.84/2.00      | X0 != u1_struct_0(sK3)
% 11.84/2.00      | sK0(k1_orders_2(sK3,k2_struct_0(sK3))) != sK0(k1_orders_2(sK3,k2_struct_0(sK3))) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_8255]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_23786,plain,
% 11.84/2.00      ( ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),u1_struct_0(sK3))
% 11.84/2.00      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3))
% 11.84/2.00      | k2_struct_0(sK3) != u1_struct_0(sK3)
% 11.84/2.00      | sK0(k1_orders_2(sK3,k2_struct_0(sK3))) != sK0(k1_orders_2(sK3,k2_struct_0(sK3))) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_20390]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_0,plain,
% 11.84/2.00      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 11.84/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1259,plain,
% 11.84/2.00      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_3,plain,
% 11.84/2.00      ( r1_tarski(X0,X0) ),
% 11.84/2.00      inference(cnf_transformation,[],[f78]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1257,plain,
% 11.84/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_7,plain,
% 11.84/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.84/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1254,plain,
% 11.84/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.84/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_25,negated_conjecture,
% 11.84/2.00      ( l1_orders_2(sK3) ),
% 11.84/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1237,plain,
% 11.84/2.00      ( l1_orders_2(sK3) = iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_17,plain,
% 11.84/2.00      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 11.84/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1244,plain,
% 11.84/2.00      ( l1_orders_2(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1855,plain,
% 11.84/2.00      ( l1_struct_0(sK3) = iProver_top ),
% 11.84/2.00      inference(superposition,[status(thm)],[c_1237,c_1244]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_11,plain,
% 11.84/2.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.84/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1250,plain,
% 11.84/2.00      ( u1_struct_0(X0) = k2_struct_0(X0)
% 11.84/2.00      | l1_struct_0(X0) != iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1982,plain,
% 11.84/2.00      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 11.84/2.00      inference(superposition,[status(thm)],[c_1855,c_1250]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_15,plain,
% 11.84/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.84/2.00      | v2_struct_0(X1)
% 11.84/2.00      | ~ v3_orders_2(X1)
% 11.84/2.00      | ~ v4_orders_2(X1)
% 11.84/2.00      | ~ v5_orders_2(X1)
% 11.84/2.00      | ~ l1_orders_2(X1)
% 11.84/2.00      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 11.84/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1246,plain,
% 11.84/2.00      ( a_2_0_orders_2(X0,X1) = k1_orders_2(X0,X1)
% 11.84/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.84/2.00      | v2_struct_0(X0) = iProver_top
% 11.84/2.00      | v3_orders_2(X0) != iProver_top
% 11.84/2.00      | v4_orders_2(X0) != iProver_top
% 11.84/2.00      | v5_orders_2(X0) != iProver_top
% 11.84/2.00      | l1_orders_2(X0) != iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_3864,plain,
% 11.84/2.00      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 11.84/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.84/2.00      | v2_struct_0(sK3) = iProver_top
% 11.84/2.00      | v3_orders_2(sK3) != iProver_top
% 11.84/2.00      | v4_orders_2(sK3) != iProver_top
% 11.84/2.00      | v5_orders_2(sK3) != iProver_top
% 11.84/2.00      | l1_orders_2(sK3) != iProver_top ),
% 11.84/2.00      inference(superposition,[status(thm)],[c_1982,c_1246]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_29,negated_conjecture,
% 11.84/2.00      ( ~ v2_struct_0(sK3) ),
% 11.84/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_30,plain,
% 11.84/2.00      ( v2_struct_0(sK3) != iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_28,negated_conjecture,
% 11.84/2.00      ( v3_orders_2(sK3) ),
% 11.84/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_31,plain,
% 11.84/2.00      ( v3_orders_2(sK3) = iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_27,negated_conjecture,
% 11.84/2.00      ( v4_orders_2(sK3) ),
% 11.84/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_32,plain,
% 11.84/2.00      ( v4_orders_2(sK3) = iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_26,negated_conjecture,
% 11.84/2.00      ( v5_orders_2(sK3) ),
% 11.84/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_33,plain,
% 11.84/2.00      ( v5_orders_2(sK3) = iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_34,plain,
% 11.84/2.00      ( l1_orders_2(sK3) = iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_4193,plain,
% 11.84/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.84/2.00      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 11.84/2.00      inference(global_propositional_subsumption,
% 11.84/2.00                [status(thm)],
% 11.84/2.00                [c_3864,c_30,c_31,c_32,c_33,c_34]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_4194,plain,
% 11.84/2.00      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 11.84/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 11.84/2.00      inference(renaming,[status(thm)],[c_4193]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_4201,plain,
% 11.84/2.00      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 11.84/2.00      | r1_tarski(X0,k2_struct_0(sK3)) != iProver_top ),
% 11.84/2.00      inference(superposition,[status(thm)],[c_1254,c_4194]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_4562,plain,
% 11.84/2.00      ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 11.84/2.00      inference(superposition,[status(thm)],[c_1257,c_4201]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_22,plain,
% 11.84/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.84/2.00      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 11.84/2.00      | v2_struct_0(X1)
% 11.84/2.00      | ~ v3_orders_2(X1)
% 11.84/2.00      | ~ v4_orders_2(X1)
% 11.84/2.00      | ~ v5_orders_2(X1)
% 11.84/2.00      | ~ l1_orders_2(X1)
% 11.84/2.00      | sK2(X2,X1,X0) = X2 ),
% 11.84/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1239,plain,
% 11.84/2.00      ( sK2(X0,X1,X2) = X0
% 11.84/2.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.84/2.00      | r2_hidden(X0,a_2_0_orders_2(X1,X2)) != iProver_top
% 11.84/2.00      | v2_struct_0(X1) = iProver_top
% 11.84/2.00      | v3_orders_2(X1) != iProver_top
% 11.84/2.00      | v4_orders_2(X1) != iProver_top
% 11.84/2.00      | v5_orders_2(X1) != iProver_top
% 11.84/2.00      | l1_orders_2(X1) != iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_2459,plain,
% 11.84/2.00      ( sK2(X0,sK3,X1) = X0
% 11.84/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.84/2.00      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 11.84/2.00      | v2_struct_0(sK3) = iProver_top
% 11.84/2.00      | v3_orders_2(sK3) != iProver_top
% 11.84/2.00      | v4_orders_2(sK3) != iProver_top
% 11.84/2.00      | v5_orders_2(sK3) != iProver_top
% 11.84/2.00      | l1_orders_2(sK3) != iProver_top ),
% 11.84/2.00      inference(superposition,[status(thm)],[c_1982,c_1239]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_3013,plain,
% 11.84/2.00      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 11.84/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.84/2.00      | sK2(X0,sK3,X1) = X0 ),
% 11.84/2.00      inference(global_propositional_subsumption,
% 11.84/2.00                [status(thm)],
% 11.84/2.00                [c_2459,c_30,c_31,c_32,c_33,c_34]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_3014,plain,
% 11.84/2.00      ( sK2(X0,sK3,X1) = X0
% 11.84/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.84/2.00      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
% 11.84/2.00      inference(renaming,[status(thm)],[c_3013]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_5096,plain,
% 11.84/2.00      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 11.84/2.00      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.84/2.00      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 11.84/2.00      inference(superposition,[status(thm)],[c_4562,c_3014]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_4117,plain,
% 11.84/2.00      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_4120,plain,
% 11.84/2.00      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) = iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_4117]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_4122,plain,
% 11.84/2.00      ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3)) = iProver_top ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_4120]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_2806,plain,
% 11.84/2.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(X0))
% 11.84/2.00      | ~ r1_tarski(k2_struct_0(sK3),X0) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_7]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_5083,plain,
% 11.84/2.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3)))
% 11.84/2.00      | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3)) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_2806]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_5087,plain,
% 11.84/2.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 11.84/2.00      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3)) != iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_5083]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_5794,plain,
% 11.84/2.00      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 11.84/2.00      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 11.84/2.00      inference(global_propositional_subsumption,
% 11.84/2.00                [status(thm)],
% 11.84/2.00                [c_5096,c_4122,c_5087]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_5802,plain,
% 11.84/2.00      ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)))
% 11.84/2.00      | k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 11.84/2.00      inference(superposition,[status(thm)],[c_1259,c_5794]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_24,negated_conjecture,
% 11.84/2.00      ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 11.84/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1574,plain,
% 11.84/2.00      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
% 11.84/2.00      | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_0]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_10,plain,
% 11.84/2.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 11.84/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1679,plain,
% 11.84/2.00      ( ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),sK0(k1_orders_2(sK3,k2_struct_0(sK3))))
% 11.84/2.00      | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_540,plain,
% 11.84/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.84/2.00      theory(equality) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1811,plain,
% 11.84/2.00      ( ~ r1_tarski(X0,sK0(k1_orders_2(sK3,k2_struct_0(sK3))))
% 11.84/2.00      | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),sK0(k1_orders_2(sK3,k2_struct_0(sK3))))
% 11.84/2.00      | k1_orders_2(sK3,k2_struct_0(sK3)) != X0 ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_540]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1968,plain,
% 11.84/2.00      ( r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),sK0(k1_orders_2(sK3,k2_struct_0(sK3))))
% 11.84/2.00      | ~ r1_tarski(k1_xboole_0,sK0(k1_orders_2(sK3,k2_struct_0(sK3))))
% 11.84/2.00      | k1_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0 ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_1811]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_4,plain,
% 11.84/2.00      ( r1_tarski(k1_xboole_0,X0) ),
% 11.84/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1969,plain,
% 11.84/2.00      ( r1_tarski(k1_xboole_0,sK0(k1_orders_2(sK3,k2_struct_0(sK3)))) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_13293,plain,
% 11.84/2.00      ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3))) ),
% 11.84/2.00      inference(global_propositional_subsumption,
% 11.84/2.00                [status(thm)],
% 11.84/2.00                [c_5802,c_24,c_1574,c_1679,c_1968,c_1969]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_21,plain,
% 11.84/2.00      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 11.84/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.84/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 11.84/2.00      | ~ r2_hidden(X1,X3)
% 11.84/2.00      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 11.84/2.00      | v2_struct_0(X0)
% 11.84/2.00      | ~ v3_orders_2(X0)
% 11.84/2.00      | ~ v4_orders_2(X0)
% 11.84/2.00      | ~ v5_orders_2(X0)
% 11.84/2.00      | ~ l1_orders_2(X0) ),
% 11.84/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1240,plain,
% 11.84/2.00      ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
% 11.84/2.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 11.84/2.00      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.84/2.00      | r2_hidden(X1,X3) != iProver_top
% 11.84/2.00      | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
% 11.84/2.00      | v2_struct_0(X0) = iProver_top
% 11.84/2.00      | v3_orders_2(X0) != iProver_top
% 11.84/2.00      | v4_orders_2(X0) != iProver_top
% 11.84/2.00      | v5_orders_2(X0) != iProver_top
% 11.84/2.00      | l1_orders_2(X0) != iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_9,plain,
% 11.84/2.00      ( m1_subset_1(X0,X1)
% 11.84/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.84/2.00      | ~ r2_hidden(X0,X2) ),
% 11.84/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1252,plain,
% 11.84/2.00      ( m1_subset_1(X0,X1) = iProver_top
% 11.84/2.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 11.84/2.00      | r2_hidden(X0,X2) != iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1472,plain,
% 11.84/2.00      ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
% 11.84/2.00      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.84/2.00      | r2_hidden(X1,X3) != iProver_top
% 11.84/2.00      | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
% 11.84/2.00      | v2_struct_0(X0) = iProver_top
% 11.84/2.00      | v3_orders_2(X0) != iProver_top
% 11.84/2.00      | v4_orders_2(X0) != iProver_top
% 11.84/2.00      | v5_orders_2(X0) != iProver_top
% 11.84/2.00      | l1_orders_2(X0) != iProver_top ),
% 11.84/2.00      inference(forward_subsumption_resolution,
% 11.84/2.00                [status(thm)],
% 11.84/2.00                [c_1240,c_1252]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_23,plain,
% 11.84/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.84/2.00      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 11.84/2.00      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 11.84/2.00      | v2_struct_0(X1)
% 11.84/2.00      | ~ v3_orders_2(X1)
% 11.84/2.00      | ~ v4_orders_2(X1)
% 11.84/2.00      | ~ v5_orders_2(X1)
% 11.84/2.00      | ~ l1_orders_2(X1) ),
% 11.84/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1238,plain,
% 11.84/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.84/2.00      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1)) = iProver_top
% 11.84/2.00      | r2_hidden(X2,a_2_0_orders_2(X1,X0)) != iProver_top
% 11.84/2.00      | v2_struct_0(X1) = iProver_top
% 11.84/2.00      | v3_orders_2(X1) != iProver_top
% 11.84/2.00      | v4_orders_2(X1) != iProver_top
% 11.84/2.00      | v5_orders_2(X1) != iProver_top
% 11.84/2.00      | l1_orders_2(X1) != iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_2093,plain,
% 11.84/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.84/2.00      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 11.84/2.00      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 11.84/2.00      | v2_struct_0(sK3) = iProver_top
% 11.84/2.00      | v3_orders_2(sK3) != iProver_top
% 11.84/2.00      | v4_orders_2(sK3) != iProver_top
% 11.84/2.00      | v5_orders_2(sK3) != iProver_top
% 11.84/2.00      | l1_orders_2(sK3) != iProver_top ),
% 11.84/2.00      inference(superposition,[status(thm)],[c_1982,c_1238]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_2094,plain,
% 11.84/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.84/2.00      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 11.84/2.00      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 11.84/2.00      | v2_struct_0(sK3) = iProver_top
% 11.84/2.00      | v3_orders_2(sK3) != iProver_top
% 11.84/2.00      | v4_orders_2(sK3) != iProver_top
% 11.84/2.00      | v5_orders_2(sK3) != iProver_top
% 11.84/2.00      | l1_orders_2(sK3) != iProver_top ),
% 11.84/2.00      inference(light_normalisation,[status(thm)],[c_2093,c_1982]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_2099,plain,
% 11.84/2.00      ( r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 11.84/2.00      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 11.84/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 11.84/2.00      inference(global_propositional_subsumption,
% 11.84/2.00                [status(thm)],
% 11.84/2.00                [c_2094,c_30,c_31,c_32,c_33,c_34]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_2100,plain,
% 11.84/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.84/2.00      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 11.84/2.00      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top ),
% 11.84/2.00      inference(renaming,[status(thm)],[c_2099]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_13,plain,
% 11.84/2.00      ( ~ r2_orders_2(X0,X1,X1)
% 11.84/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.84/2.00      | ~ l1_orders_2(X0) ),
% 11.84/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1248,plain,
% 11.84/2.00      ( r2_orders_2(X0,X1,X1) != iProver_top
% 11.84/2.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 11.84/2.00      | l1_orders_2(X0) != iProver_top ),
% 11.84/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_2860,plain,
% 11.84/2.00      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 11.84/2.00      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 11.84/2.00      | l1_orders_2(sK3) != iProver_top ),
% 11.84/2.00      inference(superposition,[status(thm)],[c_1982,c_1248]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_2890,plain,
% 11.84/2.00      ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 11.84/2.00      | r2_orders_2(sK3,X0,X0) != iProver_top ),
% 11.84/2.00      inference(global_propositional_subsumption,
% 11.84/2.00                [status(thm)],
% 11.84/2.00                [c_2860,c_34]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_2891,plain,
% 11.84/2.00      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 11.84/2.00      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 11.84/2.00      inference(renaming,[status(thm)],[c_2890]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_2898,plain,
% 11.84/2.00      ( r2_orders_2(sK3,sK2(X0,sK3,X1),sK2(X0,sK3,X1)) != iProver_top
% 11.84/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.84/2.00      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
% 11.84/2.00      inference(superposition,[status(thm)],[c_2100,c_2891]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_6467,plain,
% 11.84/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.84/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.84/2.00      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 11.84/2.00      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
% 11.84/2.00      | v2_struct_0(sK3) = iProver_top
% 11.84/2.00      | v3_orders_2(sK3) != iProver_top
% 11.84/2.00      | v4_orders_2(sK3) != iProver_top
% 11.84/2.00      | v5_orders_2(sK3) != iProver_top
% 11.84/2.00      | l1_orders_2(sK3) != iProver_top ),
% 11.84/2.00      inference(superposition,[status(thm)],[c_1472,c_2898]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_6477,plain,
% 11.84/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.84/2.00      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 11.84/2.00      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
% 11.84/2.00      | v2_struct_0(sK3) = iProver_top
% 11.84/2.00      | v3_orders_2(sK3) != iProver_top
% 11.84/2.00      | v4_orders_2(sK3) != iProver_top
% 11.84/2.00      | v5_orders_2(sK3) != iProver_top
% 11.84/2.00      | l1_orders_2(sK3) != iProver_top ),
% 11.84/2.00      inference(light_normalisation,[status(thm)],[c_6467,c_1982]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_7283,plain,
% 11.84/2.00      ( r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top
% 11.84/2.00      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 11.84/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 11.84/2.00      inference(global_propositional_subsumption,
% 11.84/2.00                [status(thm)],
% 11.84/2.00                [c_6477,c_30,c_31,c_32,c_33,c_34]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_7284,plain,
% 11.84/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.84/2.00      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 11.84/2.00      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 11.84/2.00      inference(renaming,[status(thm)],[c_7283]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_13303,plain,
% 11.84/2.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.84/2.00      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 11.84/2.00      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
% 11.84/2.00      inference(superposition,[status(thm)],[c_13293,c_7284]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_13362,plain,
% 11.84/2.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.84/2.00      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 11.84/2.00      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top ),
% 11.84/2.00      inference(light_normalisation,[status(thm)],[c_13303,c_4562]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_13447,plain,
% 11.84/2.00      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3)))
% 11.84/2.00      | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
% 11.84/2.00      | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) ),
% 11.84/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_13362]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_5,plain,
% 11.84/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.84/2.00      | ~ r2_hidden(X2,X0)
% 11.84/2.00      | r2_hidden(X2,X1) ),
% 11.84/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_197,plain,
% 11.84/2.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.84/2.00      inference(prop_impl,[status(thm)],[c_7]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_198,plain,
% 11.84/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.84/2.00      inference(renaming,[status(thm)],[c_197]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_261,plain,
% 11.84/2.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 11.84/2.00      inference(bin_hyper_res,[status(thm)],[c_5,c_198]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1664,plain,
% 11.84/2.00      ( ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X0)
% 11.84/2.00      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),X0)
% 11.84/2.00      | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_261]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_12501,plain,
% 11.84/2.00      ( ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),u1_struct_0(sK3))
% 11.84/2.00      | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
% 11.84/2.00      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),u1_struct_0(sK3)) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_1664]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1827,plain,
% 11.84/2.00      ( ~ r1_tarski(X0,X1)
% 11.84/2.00      | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X1)
% 11.84/2.00      | k1_orders_2(sK3,k2_struct_0(sK3)) != X0 ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_540]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_4669,plain,
% 11.84/2.00      ( ~ r1_tarski(k1_orders_2(X0,u1_struct_0(sK3)),X1)
% 11.84/2.00      | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X1)
% 11.84/2.00      | k1_orders_2(sK3,k2_struct_0(sK3)) != k1_orders_2(X0,u1_struct_0(sK3)) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_1827]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_10124,plain,
% 11.84/2.00      ( ~ r1_tarski(k1_orders_2(sK3,u1_struct_0(sK3)),u1_struct_0(sK3))
% 11.84/2.00      | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),u1_struct_0(sK3))
% 11.84/2.00      | k1_orders_2(sK3,k2_struct_0(sK3)) != k1_orders_2(sK3,u1_struct_0(sK3)) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_4669]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_546,plain,
% 11.84/2.00      ( X0 != X1 | X2 != X3 | k1_orders_2(X0,X2) = k1_orders_2(X1,X3) ),
% 11.84/2.00      theory(equality) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1698,plain,
% 11.84/2.00      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(X0,X1)
% 11.84/2.00      | k2_struct_0(sK3) != X1
% 11.84/2.00      | sK3 != X0 ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_546]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_4347,plain,
% 11.84/2.00      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(X0,u1_struct_0(sK3))
% 11.84/2.00      | k2_struct_0(sK3) != u1_struct_0(sK3)
% 11.84/2.00      | sK3 != X0 ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_1698]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_4348,plain,
% 11.84/2.00      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,u1_struct_0(sK3))
% 11.84/2.00      | k2_struct_0(sK3) != u1_struct_0(sK3)
% 11.84/2.00      | sK3 != sK3 ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_4347]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_4121,plain,
% 11.84/2.00      ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3)) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_4117]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_8,plain,
% 11.84/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.84/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1789,plain,
% 11.84/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.84/2.00      | r1_tarski(X0,u1_struct_0(X1)) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_3474,plain,
% 11.84/2.00      ( ~ m1_subset_1(k1_orders_2(X0,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
% 11.84/2.00      | r1_tarski(k1_orders_2(X0,u1_struct_0(X0)),u1_struct_0(X0)) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_1789]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_3486,plain,
% 11.84/2.00      ( ~ m1_subset_1(k1_orders_2(sK3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.84/2.00      | r1_tarski(k1_orders_2(sK3,u1_struct_0(sK3)),u1_struct_0(sK3)) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_3474]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_538,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1948,plain,
% 11.84/2.00      ( X0 != X1 | k2_struct_0(sK3) != X1 | k2_struct_0(sK3) = X0 ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_538]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_2418,plain,
% 11.84/2.00      ( X0 != k2_struct_0(sK3)
% 11.84/2.00      | k2_struct_0(sK3) = X0
% 11.84/2.00      | k2_struct_0(sK3) != k2_struct_0(sK3) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_1948]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_2824,plain,
% 11.84/2.00      ( u1_struct_0(sK3) != k2_struct_0(sK3)
% 11.84/2.00      | k2_struct_0(sK3) = u1_struct_0(sK3)
% 11.84/2.00      | k2_struct_0(sK3) != k2_struct_0(sK3) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_2418]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_16,plain,
% 11.84/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.84/2.00      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.84/2.00      | v2_struct_0(X1)
% 11.84/2.00      | ~ v3_orders_2(X1)
% 11.84/2.00      | ~ v4_orders_2(X1)
% 11.84/2.00      | ~ v5_orders_2(X1)
% 11.84/2.00      | ~ l1_orders_2(X1) ),
% 11.84/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_2168,plain,
% 11.84/2.00      ( m1_subset_1(k1_orders_2(X0,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
% 11.84/2.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 11.84/2.00      | v2_struct_0(X0)
% 11.84/2.00      | ~ v3_orders_2(X0)
% 11.84/2.00      | ~ v4_orders_2(X0)
% 11.84/2.00      | ~ v5_orders_2(X0)
% 11.84/2.00      | ~ l1_orders_2(X0) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_16]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_2170,plain,
% 11.84/2.00      ( m1_subset_1(k1_orders_2(sK3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.84/2.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.84/2.00      | v2_struct_0(sK3)
% 11.84/2.00      | ~ v3_orders_2(sK3)
% 11.84/2.00      | ~ v4_orders_2(sK3)
% 11.84/2.00      | ~ v5_orders_2(sK3)
% 11.84/2.00      | ~ l1_orders_2(sK3) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_2168]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_537,plain,( X0 = X0 ),theory(equality) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1920,plain,
% 11.84/2.00      ( sK0(k1_orders_2(sK3,k2_struct_0(sK3))) = sK0(k1_orders_2(sK3,k2_struct_0(sK3))) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_537]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1795,plain,
% 11.84/2.00      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1801,plain,
% 11.84/2.00      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_1795]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1606,plain,
% 11.84/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.84/2.00      | ~ r1_tarski(X0,u1_struct_0(X1)) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_7]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1794,plain,
% 11.84/2.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 11.84/2.00      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_1606]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1797,plain,
% 11.84/2.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.84/2.00      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_1794]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_543,plain,
% 11.84/2.00      ( X0 != X1 | k2_struct_0(X0) = k2_struct_0(X1) ),
% 11.84/2.00      theory(equality) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_555,plain,
% 11.84/2.00      ( k2_struct_0(sK3) = k2_struct_0(sK3) | sK3 != sK3 ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_543]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_1,plain,
% 11.84/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.84/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_98,plain,
% 11.84/2.00      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_94,plain,
% 11.84/2.00      ( r1_tarski(sK3,sK3) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_72,plain,
% 11.84/2.00      ( ~ l1_struct_0(sK3) | u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_11]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(c_54,plain,
% 11.84/2.00      ( ~ l1_orders_2(sK3) | l1_struct_0(sK3) ),
% 11.84/2.00      inference(instantiation,[status(thm)],[c_17]) ).
% 11.84/2.00  
% 11.84/2.00  cnf(contradiction,plain,
% 11.84/2.00      ( $false ),
% 11.84/2.00      inference(minisat,
% 11.84/2.00                [status(thm)],
% 11.84/2.00                [c_23786,c_13447,c_12501,c_10124,c_5083,c_4348,c_4121,
% 11.84/2.00                 c_3486,c_2824,c_2170,c_1920,c_1801,c_1797,c_1574,c_555,
% 11.84/2.00                 c_98,c_94,c_72,c_54,c_24,c_25,c_26,c_27,c_28,c_29]) ).
% 11.84/2.00  
% 11.84/2.00  
% 11.84/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.84/2.00  
% 11.84/2.00  ------                               Statistics
% 11.84/2.00  
% 11.84/2.00  ------ Selected
% 11.84/2.00  
% 11.84/2.00  total_time:                             1.123
% 11.84/2.00  
%------------------------------------------------------------------------------
