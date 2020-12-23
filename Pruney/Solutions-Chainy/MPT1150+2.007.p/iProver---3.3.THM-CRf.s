%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:06 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  170 (1476 expanded)
%              Number of clauses        :  102 ( 413 expanded)
%              Number of leaves         :   21 ( 325 expanded)
%              Depth                    :   22
%              Number of atoms          :  683 (7246 expanded)
%              Number of equality atoms :  204 (1399 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f40,plain,(
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

fof(f39,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f40,f39])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK1(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK1(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f64])).

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

fof(f42,plain,
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

fof(f43,plain,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f42])).

fof(f70,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f54,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

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

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f72,plain,(
    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f33])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_17,plain,
    ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_25,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_570,plain,
    ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_571,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1))
    | r2_hidden(sK1(sK3,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_26,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_575,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1))
    | r2_hidden(sK1(sK3,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_28,c_27,c_26,c_24])).

cnf(c_1166,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) = iProver_top
    | r2_hidden(sK1(sK3,X1,X0),X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_15,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_10,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_319,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_15,c_10])).

cnf(c_649,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_319,c_24])).

cnf(c_650,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_649])).

cnf(c_1243,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) = iProver_top
    | r2_hidden(sK1(sK3,X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1166,c_650])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1177,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_594,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_595,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_599,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_595,c_28,c_27,c_26,c_24])).

cnf(c_1165,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_1206,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1165,c_650])).

cnf(c_1528,plain,
    ( a_2_0_orders_2(sK3,k1_xboole_0) = k1_orders_2(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1177,c_1206])).

cnf(c_22,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_orders_2(X0,k1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_449,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_orders_2(X0,k1_struct_0(X0)) = u1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_25])).

cnf(c_450,plain,
    ( v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | k1_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_452,plain,
    ( k1_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_28,c_27,c_26,c_24])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_330,plain,
    ( ~ l1_orders_2(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15,c_9])).

cnf(c_644,plain,
    ( k1_struct_0(X0) = k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_330,c_24])).

cnf(c_645,plain,
    ( k1_struct_0(sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_1189,plain,
    ( k1_orders_2(sK3,k1_xboole_0) = k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_452,c_645,c_650])).

cnf(c_1529,plain,
    ( a_2_0_orders_2(sK3,k1_xboole_0) = k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_1528,c_1189])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_525,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X0,X1,X2) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_526,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(sK3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | sK2(X0,sK3,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_530,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(sK3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK2(X0,sK3,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_28,c_27,c_26,c_24])).

cnf(c_1168,plain,
    ( sK2(X0,sK3,X1) = X0
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_530])).

cnf(c_1229,plain,
    ( sK2(X0,sK3,X1) = X0
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1168,c_650])).

cnf(c_1793,plain,
    ( sK2(X0,sK3,k1_xboole_0) = X0
    | r2_hidden(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1529,c_1229])).

cnf(c_1872,plain,
    ( sK2(X0,sK3,k1_xboole_0) = X0
    | r2_hidden(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1793,c_1177])).

cnf(c_1877,plain,
    ( sK2(sK1(sK3,k2_struct_0(sK3),X0),sK3,k1_xboole_0) = sK1(sK3,k2_struct_0(sK3),X0)
    | r2_hidden(X0,a_2_0_orders_2(sK3,k2_struct_0(sK3))) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1243,c_1872])).

cnf(c_2,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1178,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1194,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1178,c_1])).

cnf(c_1532,plain,
    ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1194,c_1206])).

cnf(c_1882,plain,
    ( sK2(sK1(sK3,k2_struct_0(sK3),X0),sK3,k1_xboole_0) = sK1(sK3,k2_struct_0(sK3),X0)
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1877,c_1532])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_8,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1340,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
    | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1341,plain,
    ( k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1340])).

cnf(c_1173,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1864,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1532,c_1229])).

cnf(c_2230,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1864,c_1194])).

cnf(c_2234,plain,
    ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)))
    | k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1173,c_2230])).

cnf(c_883,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_908,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_883])).

cnf(c_884,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1345,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_1346,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
    | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_3267,plain,
    ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2234,c_23,c_908,c_1346])).

cnf(c_19,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_457,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_458,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_460,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_28,c_27,c_26,c_24])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_474,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_460,c_4])).

cnf(c_1171,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_1261,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1171,c_650])).

cnf(c_12,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_654,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_655,plain,
    ( ~ r2_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_654])).

cnf(c_1164,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_1201,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1164,c_650])).

cnf(c_1629,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1201])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_504,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_505,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(sK3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_509,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(sK3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_28,c_27,c_26,c_24])).

cnf(c_1169,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_1236,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1169,c_650])).

cnf(c_2331,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1629,c_1236])).

cnf(c_2332,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2331])).

cnf(c_3273,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3267,c_2332])).

cnf(c_3293,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3273,c_1532])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_308,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_309,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_1172,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_1694,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,k1_xboole_0)) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1243,c_1172])).

cnf(c_1939,plain,
    ( r2_hidden(X0,k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1694,c_1529])).

cnf(c_1943,plain,
    ( r2_hidden(X0,k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1939,c_1177])).

cnf(c_1947,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_1943])).

cnf(c_3274,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3267,c_1947])).

cnf(c_3286,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3274,c_1532])).

cnf(c_3296,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3293,c_3286])).

cnf(c_3808,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1882,c_23,c_1341,c_3296])).

cnf(c_3813,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3808,c_1194])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:12:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.98/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/0.99  
% 2.98/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.98/0.99  
% 2.98/0.99  ------  iProver source info
% 2.98/0.99  
% 2.98/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.98/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.98/0.99  git: non_committed_changes: false
% 2.98/0.99  git: last_make_outside_of_git: false
% 2.98/0.99  
% 2.98/0.99  ------ 
% 2.98/0.99  
% 2.98/0.99  ------ Input Options
% 2.98/0.99  
% 2.98/0.99  --out_options                           all
% 2.98/0.99  --tptp_safe_out                         true
% 2.98/0.99  --problem_path                          ""
% 2.98/0.99  --include_path                          ""
% 2.98/0.99  --clausifier                            res/vclausify_rel
% 2.98/0.99  --clausifier_options                    --mode clausify
% 2.98/0.99  --stdin                                 false
% 2.98/0.99  --stats_out                             all
% 2.98/0.99  
% 2.98/0.99  ------ General Options
% 2.98/0.99  
% 2.98/0.99  --fof                                   false
% 2.98/0.99  --time_out_real                         305.
% 2.98/0.99  --time_out_virtual                      -1.
% 2.98/0.99  --symbol_type_check                     false
% 2.98/0.99  --clausify_out                          false
% 2.98/0.99  --sig_cnt_out                           false
% 2.98/0.99  --trig_cnt_out                          false
% 2.98/0.99  --trig_cnt_out_tolerance                1.
% 2.98/0.99  --trig_cnt_out_sk_spl                   false
% 2.98/0.99  --abstr_cl_out                          false
% 2.98/0.99  
% 2.98/0.99  ------ Global Options
% 2.98/0.99  
% 2.98/0.99  --schedule                              default
% 2.98/0.99  --add_important_lit                     false
% 2.98/0.99  --prop_solver_per_cl                    1000
% 2.98/0.99  --min_unsat_core                        false
% 2.98/0.99  --soft_assumptions                      false
% 2.98/0.99  --soft_lemma_size                       3
% 2.98/0.99  --prop_impl_unit_size                   0
% 2.98/0.99  --prop_impl_unit                        []
% 2.98/0.99  --share_sel_clauses                     true
% 2.98/0.99  --reset_solvers                         false
% 2.98/0.99  --bc_imp_inh                            [conj_cone]
% 2.98/0.99  --conj_cone_tolerance                   3.
% 2.98/0.99  --extra_neg_conj                        none
% 2.98/0.99  --large_theory_mode                     true
% 2.98/0.99  --prolific_symb_bound                   200
% 2.98/0.99  --lt_threshold                          2000
% 2.98/0.99  --clause_weak_htbl                      true
% 2.98/0.99  --gc_record_bc_elim                     false
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing Options
% 2.98/0.99  
% 2.98/0.99  --preprocessing_flag                    true
% 2.98/0.99  --time_out_prep_mult                    0.1
% 2.98/0.99  --splitting_mode                        input
% 2.98/0.99  --splitting_grd                         true
% 2.98/0.99  --splitting_cvd                         false
% 2.98/0.99  --splitting_cvd_svl                     false
% 2.98/0.99  --splitting_nvd                         32
% 2.98/0.99  --sub_typing                            true
% 2.98/0.99  --prep_gs_sim                           true
% 2.98/0.99  --prep_unflatten                        true
% 2.98/0.99  --prep_res_sim                          true
% 2.98/0.99  --prep_upred                            true
% 2.98/0.99  --prep_sem_filter                       exhaustive
% 2.98/0.99  --prep_sem_filter_out                   false
% 2.98/0.99  --pred_elim                             true
% 2.98/0.99  --res_sim_input                         true
% 2.98/0.99  --eq_ax_congr_red                       true
% 2.98/0.99  --pure_diseq_elim                       true
% 2.98/0.99  --brand_transform                       false
% 2.98/0.99  --non_eq_to_eq                          false
% 2.98/0.99  --prep_def_merge                        true
% 2.98/0.99  --prep_def_merge_prop_impl              false
% 2.98/0.99  --prep_def_merge_mbd                    true
% 2.98/0.99  --prep_def_merge_tr_red                 false
% 2.98/0.99  --prep_def_merge_tr_cl                  false
% 2.98/0.99  --smt_preprocessing                     true
% 2.98/0.99  --smt_ac_axioms                         fast
% 2.98/0.99  --preprocessed_out                      false
% 2.98/0.99  --preprocessed_stats                    false
% 2.98/0.99  
% 2.98/0.99  ------ Abstraction refinement Options
% 2.98/0.99  
% 2.98/0.99  --abstr_ref                             []
% 2.98/0.99  --abstr_ref_prep                        false
% 2.98/0.99  --abstr_ref_until_sat                   false
% 2.98/0.99  --abstr_ref_sig_restrict                funpre
% 2.98/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/0.99  --abstr_ref_under                       []
% 2.98/0.99  
% 2.98/0.99  ------ SAT Options
% 2.98/0.99  
% 2.98/0.99  --sat_mode                              false
% 2.98/0.99  --sat_fm_restart_options                ""
% 2.98/0.99  --sat_gr_def                            false
% 2.98/0.99  --sat_epr_types                         true
% 2.98/0.99  --sat_non_cyclic_types                  false
% 2.98/0.99  --sat_finite_models                     false
% 2.98/0.99  --sat_fm_lemmas                         false
% 2.98/0.99  --sat_fm_prep                           false
% 2.98/0.99  --sat_fm_uc_incr                        true
% 2.98/0.99  --sat_out_model                         small
% 2.98/0.99  --sat_out_clauses                       false
% 2.98/0.99  
% 2.98/0.99  ------ QBF Options
% 2.98/0.99  
% 2.98/0.99  --qbf_mode                              false
% 2.98/0.99  --qbf_elim_univ                         false
% 2.98/0.99  --qbf_dom_inst                          none
% 2.98/0.99  --qbf_dom_pre_inst                      false
% 2.98/0.99  --qbf_sk_in                             false
% 2.98/0.99  --qbf_pred_elim                         true
% 2.98/0.99  --qbf_split                             512
% 2.98/0.99  
% 2.98/0.99  ------ BMC1 Options
% 2.98/0.99  
% 2.98/0.99  --bmc1_incremental                      false
% 2.98/0.99  --bmc1_axioms                           reachable_all
% 2.98/0.99  --bmc1_min_bound                        0
% 2.98/0.99  --bmc1_max_bound                        -1
% 2.98/0.99  --bmc1_max_bound_default                -1
% 2.98/0.99  --bmc1_symbol_reachability              true
% 2.98/0.99  --bmc1_property_lemmas                  false
% 2.98/0.99  --bmc1_k_induction                      false
% 2.98/0.99  --bmc1_non_equiv_states                 false
% 2.98/0.99  --bmc1_deadlock                         false
% 2.98/0.99  --bmc1_ucm                              false
% 2.98/0.99  --bmc1_add_unsat_core                   none
% 2.98/0.99  --bmc1_unsat_core_children              false
% 2.98/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/0.99  --bmc1_out_stat                         full
% 2.98/0.99  --bmc1_ground_init                      false
% 2.98/0.99  --bmc1_pre_inst_next_state              false
% 2.98/0.99  --bmc1_pre_inst_state                   false
% 2.98/0.99  --bmc1_pre_inst_reach_state             false
% 2.98/0.99  --bmc1_out_unsat_core                   false
% 2.98/0.99  --bmc1_aig_witness_out                  false
% 2.98/0.99  --bmc1_verbose                          false
% 2.98/0.99  --bmc1_dump_clauses_tptp                false
% 2.98/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.98/0.99  --bmc1_dump_file                        -
% 2.98/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.98/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.98/0.99  --bmc1_ucm_extend_mode                  1
% 2.98/0.99  --bmc1_ucm_init_mode                    2
% 2.98/0.99  --bmc1_ucm_cone_mode                    none
% 2.98/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.98/0.99  --bmc1_ucm_relax_model                  4
% 2.98/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.98/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/0.99  --bmc1_ucm_layered_model                none
% 2.98/0.99  --bmc1_ucm_max_lemma_size               10
% 2.98/0.99  
% 2.98/0.99  ------ AIG Options
% 2.98/0.99  
% 2.98/0.99  --aig_mode                              false
% 2.98/0.99  
% 2.98/0.99  ------ Instantiation Options
% 2.98/0.99  
% 2.98/0.99  --instantiation_flag                    true
% 2.98/0.99  --inst_sos_flag                         false
% 2.98/0.99  --inst_sos_phase                        true
% 2.98/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/0.99  --inst_lit_sel_side                     num_symb
% 2.98/0.99  --inst_solver_per_active                1400
% 2.98/0.99  --inst_solver_calls_frac                1.
% 2.98/0.99  --inst_passive_queue_type               priority_queues
% 2.98/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/0.99  --inst_passive_queues_freq              [25;2]
% 2.98/0.99  --inst_dismatching                      true
% 2.98/0.99  --inst_eager_unprocessed_to_passive     true
% 2.98/0.99  --inst_prop_sim_given                   true
% 2.98/0.99  --inst_prop_sim_new                     false
% 2.98/0.99  --inst_subs_new                         false
% 2.98/0.99  --inst_eq_res_simp                      false
% 2.98/0.99  --inst_subs_given                       false
% 2.98/0.99  --inst_orphan_elimination               true
% 2.98/0.99  --inst_learning_loop_flag               true
% 2.98/0.99  --inst_learning_start                   3000
% 2.98/0.99  --inst_learning_factor                  2
% 2.98/0.99  --inst_start_prop_sim_after_learn       3
% 2.98/0.99  --inst_sel_renew                        solver
% 2.98/0.99  --inst_lit_activity_flag                true
% 2.98/0.99  --inst_restr_to_given                   false
% 2.98/0.99  --inst_activity_threshold               500
% 2.98/0.99  --inst_out_proof                        true
% 2.98/0.99  
% 2.98/0.99  ------ Resolution Options
% 2.98/0.99  
% 2.98/0.99  --resolution_flag                       true
% 2.98/0.99  --res_lit_sel                           adaptive
% 2.98/0.99  --res_lit_sel_side                      none
% 2.98/0.99  --res_ordering                          kbo
% 2.98/0.99  --res_to_prop_solver                    active
% 2.98/0.99  --res_prop_simpl_new                    false
% 2.98/0.99  --res_prop_simpl_given                  true
% 2.98/0.99  --res_passive_queue_type                priority_queues
% 2.98/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/0.99  --res_passive_queues_freq               [15;5]
% 2.98/0.99  --res_forward_subs                      full
% 2.98/0.99  --res_backward_subs                     full
% 2.98/0.99  --res_forward_subs_resolution           true
% 2.98/0.99  --res_backward_subs_resolution          true
% 2.98/0.99  --res_orphan_elimination                true
% 2.98/0.99  --res_time_limit                        2.
% 2.98/0.99  --res_out_proof                         true
% 2.98/0.99  
% 2.98/0.99  ------ Superposition Options
% 2.98/0.99  
% 2.98/0.99  --superposition_flag                    true
% 2.98/0.99  --sup_passive_queue_type                priority_queues
% 2.98/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.98/0.99  --demod_completeness_check              fast
% 2.98/0.99  --demod_use_ground                      true
% 2.98/0.99  --sup_to_prop_solver                    passive
% 2.98/0.99  --sup_prop_simpl_new                    true
% 2.98/0.99  --sup_prop_simpl_given                  true
% 2.98/0.99  --sup_fun_splitting                     false
% 2.98/0.99  --sup_smt_interval                      50000
% 2.98/0.99  
% 2.98/0.99  ------ Superposition Simplification Setup
% 2.98/0.99  
% 2.98/0.99  --sup_indices_passive                   []
% 2.98/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_full_bw                           [BwDemod]
% 2.98/0.99  --sup_immed_triv                        [TrivRules]
% 2.98/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_immed_bw_main                     []
% 2.98/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.99  
% 2.98/0.99  ------ Combination Options
% 2.98/0.99  
% 2.98/0.99  --comb_res_mult                         3
% 2.98/0.99  --comb_sup_mult                         2
% 2.98/0.99  --comb_inst_mult                        10
% 2.98/0.99  
% 2.98/0.99  ------ Debug Options
% 2.98/0.99  
% 2.98/0.99  --dbg_backtrace                         false
% 2.98/0.99  --dbg_dump_prop_clauses                 false
% 2.98/0.99  --dbg_dump_prop_clauses_file            -
% 2.98/0.99  --dbg_out_stat                          false
% 2.98/0.99  ------ Parsing...
% 2.98/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.98/0.99  ------ Proving...
% 2.98/0.99  ------ Problem Properties 
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  clauses                                 20
% 2.98/0.99  conjectures                             1
% 2.98/0.99  EPR                                     1
% 2.98/0.99  Horn                                    17
% 2.98/0.99  unary                                   8
% 2.98/0.99  binary                                  3
% 2.98/0.99  lits                                    45
% 2.98/0.99  lits eq                                 12
% 2.98/0.99  fd_pure                                 0
% 2.98/0.99  fd_pseudo                               0
% 2.98/0.99  fd_cond                                 3
% 2.98/0.99  fd_pseudo_cond                          0
% 2.98/0.99  AC symbols                              0
% 2.98/0.99  
% 2.98/0.99  ------ Schedule dynamic 5 is on 
% 2.98/0.99  
% 2.98/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  ------ 
% 2.98/0.99  Current options:
% 2.98/0.99  ------ 
% 2.98/0.99  
% 2.98/0.99  ------ Input Options
% 2.98/0.99  
% 2.98/0.99  --out_options                           all
% 2.98/0.99  --tptp_safe_out                         true
% 2.98/0.99  --problem_path                          ""
% 2.98/0.99  --include_path                          ""
% 2.98/0.99  --clausifier                            res/vclausify_rel
% 2.98/0.99  --clausifier_options                    --mode clausify
% 2.98/0.99  --stdin                                 false
% 2.98/0.99  --stats_out                             all
% 2.98/0.99  
% 2.98/0.99  ------ General Options
% 2.98/0.99  
% 2.98/0.99  --fof                                   false
% 2.98/0.99  --time_out_real                         305.
% 2.98/0.99  --time_out_virtual                      -1.
% 2.98/0.99  --symbol_type_check                     false
% 2.98/0.99  --clausify_out                          false
% 2.98/0.99  --sig_cnt_out                           false
% 2.98/0.99  --trig_cnt_out                          false
% 2.98/0.99  --trig_cnt_out_tolerance                1.
% 2.98/0.99  --trig_cnt_out_sk_spl                   false
% 2.98/0.99  --abstr_cl_out                          false
% 2.98/0.99  
% 2.98/0.99  ------ Global Options
% 2.98/0.99  
% 2.98/0.99  --schedule                              default
% 2.98/0.99  --add_important_lit                     false
% 2.98/0.99  --prop_solver_per_cl                    1000
% 2.98/0.99  --min_unsat_core                        false
% 2.98/0.99  --soft_assumptions                      false
% 2.98/0.99  --soft_lemma_size                       3
% 2.98/0.99  --prop_impl_unit_size                   0
% 2.98/0.99  --prop_impl_unit                        []
% 2.98/0.99  --share_sel_clauses                     true
% 2.98/0.99  --reset_solvers                         false
% 2.98/0.99  --bc_imp_inh                            [conj_cone]
% 2.98/0.99  --conj_cone_tolerance                   3.
% 2.98/0.99  --extra_neg_conj                        none
% 2.98/0.99  --large_theory_mode                     true
% 2.98/0.99  --prolific_symb_bound                   200
% 2.98/0.99  --lt_threshold                          2000
% 2.98/0.99  --clause_weak_htbl                      true
% 2.98/0.99  --gc_record_bc_elim                     false
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing Options
% 2.98/0.99  
% 2.98/0.99  --preprocessing_flag                    true
% 2.98/0.99  --time_out_prep_mult                    0.1
% 2.98/0.99  --splitting_mode                        input
% 2.98/0.99  --splitting_grd                         true
% 2.98/0.99  --splitting_cvd                         false
% 2.98/0.99  --splitting_cvd_svl                     false
% 2.98/0.99  --splitting_nvd                         32
% 2.98/0.99  --sub_typing                            true
% 2.98/0.99  --prep_gs_sim                           true
% 2.98/0.99  --prep_unflatten                        true
% 2.98/0.99  --prep_res_sim                          true
% 2.98/0.99  --prep_upred                            true
% 2.98/0.99  --prep_sem_filter                       exhaustive
% 2.98/0.99  --prep_sem_filter_out                   false
% 2.98/0.99  --pred_elim                             true
% 2.98/0.99  --res_sim_input                         true
% 2.98/0.99  --eq_ax_congr_red                       true
% 2.98/0.99  --pure_diseq_elim                       true
% 2.98/0.99  --brand_transform                       false
% 2.98/0.99  --non_eq_to_eq                          false
% 2.98/0.99  --prep_def_merge                        true
% 2.98/0.99  --prep_def_merge_prop_impl              false
% 2.98/0.99  --prep_def_merge_mbd                    true
% 2.98/0.99  --prep_def_merge_tr_red                 false
% 2.98/0.99  --prep_def_merge_tr_cl                  false
% 2.98/0.99  --smt_preprocessing                     true
% 2.98/0.99  --smt_ac_axioms                         fast
% 2.98/0.99  --preprocessed_out                      false
% 2.98/0.99  --preprocessed_stats                    false
% 2.98/0.99  
% 2.98/0.99  ------ Abstraction refinement Options
% 2.98/0.99  
% 2.98/0.99  --abstr_ref                             []
% 2.98/0.99  --abstr_ref_prep                        false
% 2.98/0.99  --abstr_ref_until_sat                   false
% 2.98/0.99  --abstr_ref_sig_restrict                funpre
% 2.98/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/0.99  --abstr_ref_under                       []
% 2.98/0.99  
% 2.98/0.99  ------ SAT Options
% 2.98/0.99  
% 2.98/0.99  --sat_mode                              false
% 2.98/0.99  --sat_fm_restart_options                ""
% 2.98/0.99  --sat_gr_def                            false
% 2.98/0.99  --sat_epr_types                         true
% 2.98/0.99  --sat_non_cyclic_types                  false
% 2.98/0.99  --sat_finite_models                     false
% 2.98/0.99  --sat_fm_lemmas                         false
% 2.98/0.99  --sat_fm_prep                           false
% 2.98/0.99  --sat_fm_uc_incr                        true
% 2.98/0.99  --sat_out_model                         small
% 2.98/0.99  --sat_out_clauses                       false
% 2.98/0.99  
% 2.98/0.99  ------ QBF Options
% 2.98/0.99  
% 2.98/0.99  --qbf_mode                              false
% 2.98/0.99  --qbf_elim_univ                         false
% 2.98/0.99  --qbf_dom_inst                          none
% 2.98/0.99  --qbf_dom_pre_inst                      false
% 2.98/0.99  --qbf_sk_in                             false
% 2.98/0.99  --qbf_pred_elim                         true
% 2.98/0.99  --qbf_split                             512
% 2.98/0.99  
% 2.98/0.99  ------ BMC1 Options
% 2.98/0.99  
% 2.98/0.99  --bmc1_incremental                      false
% 2.98/0.99  --bmc1_axioms                           reachable_all
% 2.98/0.99  --bmc1_min_bound                        0
% 2.98/0.99  --bmc1_max_bound                        -1
% 2.98/0.99  --bmc1_max_bound_default                -1
% 2.98/0.99  --bmc1_symbol_reachability              true
% 2.98/0.99  --bmc1_property_lemmas                  false
% 2.98/0.99  --bmc1_k_induction                      false
% 2.98/0.99  --bmc1_non_equiv_states                 false
% 2.98/0.99  --bmc1_deadlock                         false
% 2.98/0.99  --bmc1_ucm                              false
% 2.98/0.99  --bmc1_add_unsat_core                   none
% 2.98/0.99  --bmc1_unsat_core_children              false
% 2.98/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/0.99  --bmc1_out_stat                         full
% 2.98/0.99  --bmc1_ground_init                      false
% 2.98/0.99  --bmc1_pre_inst_next_state              false
% 2.98/0.99  --bmc1_pre_inst_state                   false
% 2.98/0.99  --bmc1_pre_inst_reach_state             false
% 2.98/0.99  --bmc1_out_unsat_core                   false
% 2.98/0.99  --bmc1_aig_witness_out                  false
% 2.98/0.99  --bmc1_verbose                          false
% 2.98/0.99  --bmc1_dump_clauses_tptp                false
% 2.98/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.98/0.99  --bmc1_dump_file                        -
% 2.98/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.98/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.98/0.99  --bmc1_ucm_extend_mode                  1
% 2.98/0.99  --bmc1_ucm_init_mode                    2
% 2.98/0.99  --bmc1_ucm_cone_mode                    none
% 2.98/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.98/0.99  --bmc1_ucm_relax_model                  4
% 2.98/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.98/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/0.99  --bmc1_ucm_layered_model                none
% 2.98/0.99  --bmc1_ucm_max_lemma_size               10
% 2.98/0.99  
% 2.98/0.99  ------ AIG Options
% 2.98/0.99  
% 2.98/0.99  --aig_mode                              false
% 2.98/0.99  
% 2.98/0.99  ------ Instantiation Options
% 2.98/0.99  
% 2.98/0.99  --instantiation_flag                    true
% 2.98/0.99  --inst_sos_flag                         false
% 2.98/0.99  --inst_sos_phase                        true
% 2.98/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/0.99  --inst_lit_sel_side                     none
% 2.98/0.99  --inst_solver_per_active                1400
% 2.98/0.99  --inst_solver_calls_frac                1.
% 2.98/0.99  --inst_passive_queue_type               priority_queues
% 2.98/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/0.99  --inst_passive_queues_freq              [25;2]
% 2.98/0.99  --inst_dismatching                      true
% 2.98/0.99  --inst_eager_unprocessed_to_passive     true
% 2.98/0.99  --inst_prop_sim_given                   true
% 2.98/0.99  --inst_prop_sim_new                     false
% 2.98/0.99  --inst_subs_new                         false
% 2.98/0.99  --inst_eq_res_simp                      false
% 2.98/0.99  --inst_subs_given                       false
% 2.98/0.99  --inst_orphan_elimination               true
% 2.98/0.99  --inst_learning_loop_flag               true
% 2.98/0.99  --inst_learning_start                   3000
% 2.98/0.99  --inst_learning_factor                  2
% 2.98/0.99  --inst_start_prop_sim_after_learn       3
% 2.98/0.99  --inst_sel_renew                        solver
% 2.98/0.99  --inst_lit_activity_flag                true
% 2.98/0.99  --inst_restr_to_given                   false
% 2.98/0.99  --inst_activity_threshold               500
% 2.98/0.99  --inst_out_proof                        true
% 2.98/0.99  
% 2.98/0.99  ------ Resolution Options
% 2.98/0.99  
% 2.98/0.99  --resolution_flag                       false
% 2.98/0.99  --res_lit_sel                           adaptive
% 2.98/0.99  --res_lit_sel_side                      none
% 2.98/1.00  --res_ordering                          kbo
% 2.98/1.00  --res_to_prop_solver                    active
% 2.98/1.00  --res_prop_simpl_new                    false
% 2.98/1.00  --res_prop_simpl_given                  true
% 2.98/1.00  --res_passive_queue_type                priority_queues
% 2.98/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/1.00  --res_passive_queues_freq               [15;5]
% 2.98/1.00  --res_forward_subs                      full
% 2.98/1.00  --res_backward_subs                     full
% 2.98/1.00  --res_forward_subs_resolution           true
% 2.98/1.00  --res_backward_subs_resolution          true
% 2.98/1.00  --res_orphan_elimination                true
% 2.98/1.00  --res_time_limit                        2.
% 2.98/1.00  --res_out_proof                         true
% 2.98/1.00  
% 2.98/1.00  ------ Superposition Options
% 2.98/1.00  
% 2.98/1.00  --superposition_flag                    true
% 2.98/1.00  --sup_passive_queue_type                priority_queues
% 2.98/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.98/1.00  --demod_completeness_check              fast
% 2.98/1.00  --demod_use_ground                      true
% 2.98/1.00  --sup_to_prop_solver                    passive
% 2.98/1.00  --sup_prop_simpl_new                    true
% 2.98/1.00  --sup_prop_simpl_given                  true
% 2.98/1.00  --sup_fun_splitting                     false
% 2.98/1.00  --sup_smt_interval                      50000
% 2.98/1.00  
% 2.98/1.00  ------ Superposition Simplification Setup
% 2.98/1.00  
% 2.98/1.00  --sup_indices_passive                   []
% 2.98/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.00  --sup_full_bw                           [BwDemod]
% 2.98/1.00  --sup_immed_triv                        [TrivRules]
% 2.98/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.00  --sup_immed_bw_main                     []
% 2.98/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/1.00  
% 2.98/1.00  ------ Combination Options
% 2.98/1.00  
% 2.98/1.00  --comb_res_mult                         3
% 2.98/1.00  --comb_sup_mult                         2
% 2.98/1.00  --comb_inst_mult                        10
% 2.98/1.00  
% 2.98/1.00  ------ Debug Options
% 2.98/1.00  
% 2.98/1.00  --dbg_backtrace                         false
% 2.98/1.00  --dbg_dump_prop_clauses                 false
% 2.98/1.00  --dbg_dump_prop_clauses_file            -
% 2.98/1.00  --dbg_out_stat                          false
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  ------ Proving...
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  % SZS status Theorem for theBenchmark.p
% 2.98/1.00  
% 2.98/1.00   Resolution empty clause
% 2.98/1.00  
% 2.98/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.98/1.00  
% 2.98/1.00  fof(f13,axiom,(
% 2.98/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f27,plain,(
% 2.98/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 2.98/1.00    inference(ennf_transformation,[],[f13])).
% 2.98/1.00  
% 2.98/1.00  fof(f28,plain,(
% 2.98/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.98/1.00    inference(flattening,[],[f27])).
% 2.98/1.00  
% 2.98/1.00  fof(f37,plain,(
% 2.98/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.98/1.00    inference(nnf_transformation,[],[f28])).
% 2.98/1.00  
% 2.98/1.00  fof(f38,plain,(
% 2.98/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.98/1.00    inference(rectify,[],[f37])).
% 2.98/1.00  
% 2.98/1.00  fof(f40,plain,(
% 2.98/1.00    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 2.98/1.00    introduced(choice_axiom,[])).
% 2.98/1.00  
% 2.98/1.00  fof(f39,plain,(
% 2.98/1.00    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 2.98/1.00    introduced(choice_axiom,[])).
% 2.98/1.00  
% 2.98/1.00  fof(f41,plain,(
% 2.98/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.98/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f40,f39])).
% 2.98/1.00  
% 2.98/1.00  fof(f64,plain,(
% 2.98/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.98/1.00    inference(cnf_transformation,[],[f41])).
% 2.98/1.00  
% 2.98/1.00  fof(f75,plain,(
% 2.98/1.00    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_0_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.98/1.00    inference(equality_resolution,[],[f64])).
% 2.98/1.00  
% 2.98/1.00  fof(f15,conjecture,(
% 2.98/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f16,negated_conjecture,(
% 2.98/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 2.98/1.00    inference(negated_conjecture,[],[f15])).
% 2.98/1.00  
% 2.98/1.00  fof(f31,plain,(
% 2.98/1.00    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.98/1.00    inference(ennf_transformation,[],[f16])).
% 2.98/1.00  
% 2.98/1.00  fof(f32,plain,(
% 2.98/1.00    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.98/1.00    inference(flattening,[],[f31])).
% 2.98/1.00  
% 2.98/1.00  fof(f42,plain,(
% 2.98/1.00    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 2.98/1.00    introduced(choice_axiom,[])).
% 2.98/1.00  
% 2.98/1.00  fof(f43,plain,(
% 2.98/1.00    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 2.98/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f42])).
% 2.98/1.00  
% 2.98/1.00  fof(f70,plain,(
% 2.98/1.00    v5_orders_2(sK3)),
% 2.98/1.00    inference(cnf_transformation,[],[f43])).
% 2.98/1.00  
% 2.98/1.00  fof(f67,plain,(
% 2.98/1.00    ~v2_struct_0(sK3)),
% 2.98/1.00    inference(cnf_transformation,[],[f43])).
% 2.98/1.00  
% 2.98/1.00  fof(f68,plain,(
% 2.98/1.00    v3_orders_2(sK3)),
% 2.98/1.00    inference(cnf_transformation,[],[f43])).
% 2.98/1.00  
% 2.98/1.00  fof(f69,plain,(
% 2.98/1.00    v4_orders_2(sK3)),
% 2.98/1.00    inference(cnf_transformation,[],[f43])).
% 2.98/1.00  
% 2.98/1.00  fof(f71,plain,(
% 2.98/1.00    l1_orders_2(sK3)),
% 2.98/1.00    inference(cnf_transformation,[],[f43])).
% 2.98/1.00  
% 2.98/1.00  fof(f12,axiom,(
% 2.98/1.00    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f26,plain,(
% 2.98/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.98/1.00    inference(ennf_transformation,[],[f12])).
% 2.98/1.00  
% 2.98/1.00  fof(f59,plain,(
% 2.98/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.98/1.00    inference(cnf_transformation,[],[f26])).
% 2.98/1.00  
% 2.98/1.00  fof(f9,axiom,(
% 2.98/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f22,plain,(
% 2.98/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.98/1.00    inference(ennf_transformation,[],[f9])).
% 2.98/1.00  
% 2.98/1.00  fof(f54,plain,(
% 2.98/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.98/1.00    inference(cnf_transformation,[],[f22])).
% 2.98/1.00  
% 2.98/1.00  fof(f4,axiom,(
% 2.98/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f47,plain,(
% 2.98/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.98/1.00    inference(cnf_transformation,[],[f4])).
% 2.98/1.00  
% 2.98/1.00  fof(f11,axiom,(
% 2.98/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f24,plain,(
% 2.98/1.00    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.98/1.00    inference(ennf_transformation,[],[f11])).
% 2.98/1.00  
% 2.98/1.00  fof(f25,plain,(
% 2.98/1.00    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.98/1.00    inference(flattening,[],[f24])).
% 2.98/1.00  
% 2.98/1.00  fof(f58,plain,(
% 2.98/1.00    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.98/1.00    inference(cnf_transformation,[],[f25])).
% 2.98/1.00  
% 2.98/1.00  fof(f14,axiom,(
% 2.98/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)))),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f29,plain,(
% 2.98/1.00    ! [X0] : (u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.98/1.00    inference(ennf_transformation,[],[f14])).
% 2.98/1.00  
% 2.98/1.00  fof(f30,plain,(
% 2.98/1.00    ! [X0] : (u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.98/1.00    inference(flattening,[],[f29])).
% 2.98/1.00  
% 2.98/1.00  fof(f66,plain,(
% 2.98/1.00    ( ! [X0] : (u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.98/1.00    inference(cnf_transformation,[],[f30])).
% 2.98/1.00  
% 2.98/1.00  fof(f8,axiom,(
% 2.98/1.00    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f21,plain,(
% 2.98/1.00    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.98/1.00    inference(ennf_transformation,[],[f8])).
% 2.98/1.00  
% 2.98/1.00  fof(f53,plain,(
% 2.98/1.00    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.98/1.00    inference(cnf_transformation,[],[f21])).
% 2.98/1.00  
% 2.98/1.00  fof(f61,plain,(
% 2.98/1.00    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.98/1.00    inference(cnf_transformation,[],[f41])).
% 2.98/1.00  
% 2.98/1.00  fof(f3,axiom,(
% 2.98/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f46,plain,(
% 2.98/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.98/1.00    inference(cnf_transformation,[],[f3])).
% 2.98/1.00  
% 2.98/1.00  fof(f2,axiom,(
% 2.98/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f45,plain,(
% 2.98/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.98/1.00    inference(cnf_transformation,[],[f2])).
% 2.98/1.00  
% 2.98/1.00  fof(f72,plain,(
% 2.98/1.00    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))),
% 2.98/1.00    inference(cnf_transformation,[],[f43])).
% 2.98/1.00  
% 2.98/1.00  fof(f7,axiom,(
% 2.98/1.00    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f20,plain,(
% 2.98/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.98/1.00    inference(ennf_transformation,[],[f7])).
% 2.98/1.00  
% 2.98/1.00  fof(f33,plain,(
% 2.98/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 2.98/1.00    introduced(choice_axiom,[])).
% 2.98/1.00  
% 2.98/1.00  fof(f34,plain,(
% 2.98/1.00    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 2.98/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f33])).
% 2.98/1.00  
% 2.98/1.00  fof(f50,plain,(
% 2.98/1.00    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.98/1.00    inference(cnf_transformation,[],[f34])).
% 2.98/1.00  
% 2.98/1.00  fof(f62,plain,(
% 2.98/1.00    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.98/1.00    inference(cnf_transformation,[],[f41])).
% 2.98/1.00  
% 2.98/1.00  fof(f5,axiom,(
% 2.98/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f17,plain,(
% 2.98/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.98/1.00    inference(ennf_transformation,[],[f5])).
% 2.98/1.00  
% 2.98/1.00  fof(f18,plain,(
% 2.98/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.98/1.00    inference(flattening,[],[f17])).
% 2.98/1.00  
% 2.98/1.00  fof(f48,plain,(
% 2.98/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.98/1.00    inference(cnf_transformation,[],[f18])).
% 2.98/1.00  
% 2.98/1.00  fof(f10,axiom,(
% 2.98/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f23,plain,(
% 2.98/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.98/1.00    inference(ennf_transformation,[],[f10])).
% 2.98/1.00  
% 2.98/1.00  fof(f35,plain,(
% 2.98/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.98/1.00    inference(nnf_transformation,[],[f23])).
% 2.98/1.00  
% 2.98/1.00  fof(f36,plain,(
% 2.98/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.98/1.00    inference(flattening,[],[f35])).
% 2.98/1.00  
% 2.98/1.00  fof(f56,plain,(
% 2.98/1.00    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.98/1.00    inference(cnf_transformation,[],[f36])).
% 2.98/1.00  
% 2.98/1.00  fof(f73,plain,(
% 2.98/1.00    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.98/1.00    inference(equality_resolution,[],[f56])).
% 2.98/1.00  
% 2.98/1.00  fof(f60,plain,(
% 2.98/1.00    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.98/1.00    inference(cnf_transformation,[],[f41])).
% 2.98/1.00  
% 2.98/1.00  fof(f1,axiom,(
% 2.98/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f44,plain,(
% 2.98/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.98/1.00    inference(cnf_transformation,[],[f1])).
% 2.98/1.00  
% 2.98/1.00  fof(f6,axiom,(
% 2.98/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f19,plain,(
% 2.98/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.98/1.00    inference(ennf_transformation,[],[f6])).
% 2.98/1.00  
% 2.98/1.00  fof(f49,plain,(
% 2.98/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.98/1.00    inference(cnf_transformation,[],[f19])).
% 2.98/1.00  
% 2.98/1.00  cnf(c_17,plain,
% 2.98/1.00      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 2.98/1.00      | r2_hidden(sK1(X1,X2,X0),X2)
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.98/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.98/1.00      | v2_struct_0(X1)
% 2.98/1.00      | ~ v3_orders_2(X1)
% 2.98/1.00      | ~ v4_orders_2(X1)
% 2.98/1.00      | ~ v5_orders_2(X1)
% 2.98/1.00      | ~ l1_orders_2(X1) ),
% 2.98/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_25,negated_conjecture,
% 2.98/1.00      ( v5_orders_2(sK3) ),
% 2.98/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_570,plain,
% 2.98/1.00      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 2.98/1.00      | r2_hidden(sK1(X1,X2,X0),X2)
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.98/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.98/1.00      | v2_struct_0(X1)
% 2.98/1.00      | ~ v3_orders_2(X1)
% 2.98/1.00      | ~ v4_orders_2(X1)
% 2.98/1.00      | ~ l1_orders_2(X1)
% 2.98/1.00      | sK3 != X1 ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_571,plain,
% 2.98/1.00      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1))
% 2.98/1.00      | r2_hidden(sK1(sK3,X1,X0),X1)
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.98/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.98/1.00      | v2_struct_0(sK3)
% 2.98/1.00      | ~ v3_orders_2(sK3)
% 2.98/1.00      | ~ v4_orders_2(sK3)
% 2.98/1.00      | ~ l1_orders_2(sK3) ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_570]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_28,negated_conjecture,
% 2.98/1.00      ( ~ v2_struct_0(sK3) ),
% 2.98/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_27,negated_conjecture,
% 2.98/1.00      ( v3_orders_2(sK3) ),
% 2.98/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_26,negated_conjecture,
% 2.98/1.00      ( v4_orders_2(sK3) ),
% 2.98/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_24,negated_conjecture,
% 2.98/1.00      ( l1_orders_2(sK3) ),
% 2.98/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_575,plain,
% 2.98/1.00      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1))
% 2.98/1.00      | r2_hidden(sK1(sK3,X1,X0),X1)
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.98/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_571,c_28,c_27,c_26,c_24]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1166,plain,
% 2.98/1.00      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) = iProver_top
% 2.98/1.00      | r2_hidden(sK1(sK3,X1,X0),X1) = iProver_top
% 2.98/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.98/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_575]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_15,plain,
% 2.98/1.00      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_10,plain,
% 2.98/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_319,plain,
% 2.98/1.00      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.98/1.00      inference(resolution,[status(thm)],[c_15,c_10]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_649,plain,
% 2.98/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_319,c_24]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_650,plain,
% 2.98/1.00      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_649]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1243,plain,
% 2.98/1.00      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) = iProver_top
% 2.98/1.00      | r2_hidden(sK1(sK3,X1,X0),X1) = iProver_top
% 2.98/1.00      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 2.98/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_1166,c_650]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3,plain,
% 2.98/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.98/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1177,plain,
% 2.98/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_14,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.98/1.00      | v2_struct_0(X1)
% 2.98/1.00      | ~ v3_orders_2(X1)
% 2.98/1.00      | ~ v4_orders_2(X1)
% 2.98/1.00      | ~ v5_orders_2(X1)
% 2.98/1.00      | ~ l1_orders_2(X1)
% 2.98/1.00      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_594,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.98/1.00      | v2_struct_0(X1)
% 2.98/1.00      | ~ v3_orders_2(X1)
% 2.98/1.00      | ~ v4_orders_2(X1)
% 2.98/1.00      | ~ l1_orders_2(X1)
% 2.98/1.00      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
% 2.98/1.00      | sK3 != X1 ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_595,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.98/1.00      | v2_struct_0(sK3)
% 2.98/1.00      | ~ v3_orders_2(sK3)
% 2.98/1.00      | ~ v4_orders_2(sK3)
% 2.98/1.00      | ~ l1_orders_2(sK3)
% 2.98/1.00      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_594]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_599,plain,
% 2.98/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.98/1.00      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_595,c_28,c_27,c_26,c_24]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1165,plain,
% 2.98/1.00      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 2.98/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1206,plain,
% 2.98/1.00      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 2.98/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_1165,c_650]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1528,plain,
% 2.98/1.00      ( a_2_0_orders_2(sK3,k1_xboole_0) = k1_orders_2(sK3,k1_xboole_0) ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1177,c_1206]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_22,plain,
% 2.98/1.00      ( v2_struct_0(X0)
% 2.98/1.00      | ~ v3_orders_2(X0)
% 2.98/1.00      | ~ v4_orders_2(X0)
% 2.98/1.00      | ~ v5_orders_2(X0)
% 2.98/1.00      | ~ l1_orders_2(X0)
% 2.98/1.00      | k1_orders_2(X0,k1_struct_0(X0)) = u1_struct_0(X0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_449,plain,
% 2.98/1.00      ( v2_struct_0(X0)
% 2.98/1.00      | ~ v3_orders_2(X0)
% 2.98/1.00      | ~ v4_orders_2(X0)
% 2.98/1.00      | ~ l1_orders_2(X0)
% 2.98/1.00      | k1_orders_2(X0,k1_struct_0(X0)) = u1_struct_0(X0)
% 2.98/1.00      | sK3 != X0 ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_25]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_450,plain,
% 2.98/1.00      ( v2_struct_0(sK3)
% 2.98/1.00      | ~ v3_orders_2(sK3)
% 2.98/1.00      | ~ v4_orders_2(sK3)
% 2.98/1.00      | ~ l1_orders_2(sK3)
% 2.98/1.00      | k1_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_449]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_452,plain,
% 2.98/1.00      ( k1_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_450,c_28,c_27,c_26,c_24]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_9,plain,
% 2.98/1.00      ( ~ l1_struct_0(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 2.98/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_330,plain,
% 2.98/1.00      ( ~ l1_orders_2(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 2.98/1.00      inference(resolution,[status(thm)],[c_15,c_9]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_644,plain,
% 2.98/1.00      ( k1_struct_0(X0) = k1_xboole_0 | sK3 != X0 ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_330,c_24]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_645,plain,
% 2.98/1.00      ( k1_struct_0(sK3) = k1_xboole_0 ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_644]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1189,plain,
% 2.98/1.00      ( k1_orders_2(sK3,k1_xboole_0) = k2_struct_0(sK3) ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_452,c_645,c_650]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1529,plain,
% 2.98/1.00      ( a_2_0_orders_2(sK3,k1_xboole_0) = k2_struct_0(sK3) ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_1528,c_1189]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_20,plain,
% 2.98/1.00      ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 2.98/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.98/1.00      | v2_struct_0(X1)
% 2.98/1.00      | ~ v3_orders_2(X1)
% 2.98/1.00      | ~ v4_orders_2(X1)
% 2.98/1.00      | ~ v5_orders_2(X1)
% 2.98/1.00      | ~ l1_orders_2(X1)
% 2.98/1.00      | sK2(X0,X1,X2) = X0 ),
% 2.98/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_525,plain,
% 2.98/1.00      ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 2.98/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.98/1.00      | v2_struct_0(X1)
% 2.98/1.00      | ~ v3_orders_2(X1)
% 2.98/1.00      | ~ v4_orders_2(X1)
% 2.98/1.00      | ~ l1_orders_2(X1)
% 2.98/1.00      | sK2(X0,X1,X2) = X0
% 2.98/1.00      | sK3 != X1 ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_526,plain,
% 2.98/1.00      ( ~ r2_hidden(X0,a_2_0_orders_2(sK3,X1))
% 2.98/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.98/1.00      | v2_struct_0(sK3)
% 2.98/1.00      | ~ v3_orders_2(sK3)
% 2.98/1.00      | ~ v4_orders_2(sK3)
% 2.98/1.00      | ~ l1_orders_2(sK3)
% 2.98/1.00      | sK2(X0,sK3,X1) = X0 ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_525]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_530,plain,
% 2.98/1.00      ( ~ r2_hidden(X0,a_2_0_orders_2(sK3,X1))
% 2.98/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.98/1.00      | sK2(X0,sK3,X1) = X0 ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_526,c_28,c_27,c_26,c_24]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1168,plain,
% 2.98/1.00      ( sK2(X0,sK3,X1) = X0
% 2.98/1.00      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 2.98/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_530]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1229,plain,
% 2.98/1.00      ( sK2(X0,sK3,X1) = X0
% 2.98/1.00      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 2.98/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_1168,c_650]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1793,plain,
% 2.98/1.00      ( sK2(X0,sK3,k1_xboole_0) = X0
% 2.98/1.00      | r2_hidden(X0,k2_struct_0(sK3)) != iProver_top
% 2.98/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1529,c_1229]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1872,plain,
% 2.98/1.00      ( sK2(X0,sK3,k1_xboole_0) = X0
% 2.98/1.00      | r2_hidden(X0,k2_struct_0(sK3)) != iProver_top ),
% 2.98/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1793,c_1177]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1877,plain,
% 2.98/1.00      ( sK2(sK1(sK3,k2_struct_0(sK3),X0),sK3,k1_xboole_0) = sK1(sK3,k2_struct_0(sK3),X0)
% 2.98/1.00      | r2_hidden(X0,a_2_0_orders_2(sK3,k2_struct_0(sK3))) = iProver_top
% 2.98/1.00      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 2.98/1.00      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1243,c_1872]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2,plain,
% 2.98/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.98/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1178,plain,
% 2.98/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1,plain,
% 2.98/1.00      ( k2_subset_1(X0) = X0 ),
% 2.98/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1194,plain,
% 2.98/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_1178,c_1]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1532,plain,
% 2.98/1.00      ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1194,c_1206]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1882,plain,
% 2.98/1.00      ( sK2(sK1(sK3,k2_struct_0(sK3),X0),sK3,k1_xboole_0) = sK1(sK3,k2_struct_0(sK3),X0)
% 2.98/1.00      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) = iProver_top
% 2.98/1.00      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 2.98/1.00      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_1877,c_1532]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_23,negated_conjecture,
% 2.98/1.00      ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.98/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_8,plain,
% 2.98/1.00      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.98/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1340,plain,
% 2.98/1.00      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
% 2.98/1.00      | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1341,plain,
% 2.98/1.00      ( k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
% 2.98/1.00      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) = iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_1340]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1173,plain,
% 2.98/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1864,plain,
% 2.98/1.00      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 2.98/1.00      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.98/1.00      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1532,c_1229]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2230,plain,
% 2.98/1.00      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 2.98/1.00      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1864,c_1194]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2234,plain,
% 2.98/1.00      ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)))
% 2.98/1.00      | k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1173,c_2230]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_883,plain,( X0 = X0 ),theory(equality) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_908,plain,
% 2.98/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_883]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_884,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1345,plain,
% 2.98/1.00      ( k1_orders_2(sK3,k2_struct_0(sK3)) != X0
% 2.98/1.00      | k1_xboole_0 != X0
% 2.98/1.00      | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_884]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1346,plain,
% 2.98/1.00      ( k1_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
% 2.98/1.00      | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
% 2.98/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.98/1.00      inference(instantiation,[status(thm)],[c_1345]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3267,plain,
% 2.98/1.00      ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3))) ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_2234,c_23,c_908,c_1346]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_19,plain,
% 2.98/1.00      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 2.98/1.00      | ~ r2_hidden(X1,X3)
% 2.98/1.00      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.98/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.98/1.00      | v2_struct_0(X0)
% 2.98/1.00      | ~ v3_orders_2(X0)
% 2.98/1.00      | ~ v4_orders_2(X0)
% 2.98/1.00      | ~ v5_orders_2(X0)
% 2.98/1.00      | ~ l1_orders_2(X0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_457,plain,
% 2.98/1.00      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 2.98/1.00      | ~ r2_hidden(X1,X3)
% 2.98/1.00      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.98/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.98/1.00      | v2_struct_0(X0)
% 2.98/1.00      | ~ v3_orders_2(X0)
% 2.98/1.00      | ~ v4_orders_2(X0)
% 2.98/1.00      | ~ l1_orders_2(X0)
% 2.98/1.00      | sK3 != X0 ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_458,plain,
% 2.98/1.00      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 2.98/1.00      | ~ r2_hidden(X0,X2)
% 2.98/1.00      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.98/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.98/1.00      | v2_struct_0(sK3)
% 2.98/1.00      | ~ v3_orders_2(sK3)
% 2.98/1.00      | ~ v4_orders_2(sK3)
% 2.98/1.00      | ~ l1_orders_2(sK3) ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_457]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_460,plain,
% 2.98/1.00      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 2.98/1.00      | ~ r2_hidden(X0,X2)
% 2.98/1.00      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
% 2.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.98/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_458,c_28,c_27,c_26,c_24]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_4,plain,
% 2.98/1.00      ( ~ r2_hidden(X0,X1)
% 2.98/1.00      | m1_subset_1(X0,X2)
% 2.98/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.98/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_474,plain,
% 2.98/1.00      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 2.98/1.00      | ~ r2_hidden(X0,X2)
% 2.98/1.00      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
% 2.98/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.98/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_460,c_4]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1171,plain,
% 2.98/1.00      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
% 2.98/1.00      | r2_hidden(X0,X2) != iProver_top
% 2.98/1.00      | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top
% 2.98/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1261,plain,
% 2.98/1.00      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
% 2.98/1.00      | r2_hidden(X0,X2) != iProver_top
% 2.98/1.00      | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top
% 2.98/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_1171,c_650]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_12,plain,
% 2.98/1.00      ( ~ r2_orders_2(X0,X1,X1)
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.98/1.00      | ~ l1_orders_2(X0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_654,plain,
% 2.98/1.00      ( ~ r2_orders_2(X0,X1,X1)
% 2.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.98/1.00      | sK3 != X0 ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_655,plain,
% 2.98/1.00      ( ~ r2_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_654]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1164,plain,
% 2.98/1.00      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 2.98/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_655]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1201,plain,
% 2.98/1.00      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 2.98/1.00      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_1164,c_650]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1629,plain,
% 2.98/1.00      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 2.98/1.00      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 2.98/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.98/1.00      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) != iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1261,c_1201]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_21,plain,
% 2.98/1.00      ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 2.98/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.98/1.00      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 2.98/1.00      | v2_struct_0(X1)
% 2.98/1.00      | ~ v3_orders_2(X1)
% 2.98/1.00      | ~ v4_orders_2(X1)
% 2.98/1.00      | ~ v5_orders_2(X1)
% 2.98/1.00      | ~ l1_orders_2(X1) ),
% 2.98/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_504,plain,
% 2.98/1.00      ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 2.98/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.98/1.00      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 2.98/1.00      | v2_struct_0(X1)
% 2.98/1.00      | ~ v3_orders_2(X1)
% 2.98/1.00      | ~ v4_orders_2(X1)
% 2.98/1.00      | ~ l1_orders_2(X1)
% 2.98/1.00      | sK3 != X1 ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_505,plain,
% 2.98/1.00      ( ~ r2_hidden(X0,a_2_0_orders_2(sK3,X1))
% 2.98/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.98/1.00      | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3))
% 2.98/1.00      | v2_struct_0(sK3)
% 2.98/1.00      | ~ v3_orders_2(sK3)
% 2.98/1.00      | ~ v4_orders_2(sK3)
% 2.98/1.00      | ~ l1_orders_2(sK3) ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_504]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_509,plain,
% 2.98/1.00      ( ~ r2_hidden(X0,a_2_0_orders_2(sK3,X1))
% 2.98/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.98/1.00      | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_505,c_28,c_27,c_26,c_24]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1169,plain,
% 2.98/1.00      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 2.98/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.98/1.00      | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) = iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1236,plain,
% 2.98/1.00      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 2.98/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.98/1.00      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_1169,c_650]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2331,plain,
% 2.98/1.00      ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.98/1.00      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 2.98/1.00      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
% 2.98/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1629,c_1236]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_2332,plain,
% 2.98/1.00      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 2.98/1.00      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 2.98/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(renaming,[status(thm)],[c_2331]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3273,plain,
% 2.98/1.00      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.98/1.00      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top
% 2.98/1.00      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_3267,c_2332]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3293,plain,
% 2.98/1.00      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.98/1.00      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top
% 2.98/1.00      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_3273,c_1532]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_0,plain,
% 2.98/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_5,plain,
% 2.98/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.98/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_308,plain,
% 2.98/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.98/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_5]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_309,plain,
% 2.98/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.98/1.00      inference(unflattening,[status(thm)],[c_308]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1172,plain,
% 2.98/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.98/1.00      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1694,plain,
% 2.98/1.00      ( r2_hidden(X0,a_2_0_orders_2(sK3,k1_xboole_0)) = iProver_top
% 2.98/1.00      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 2.98/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1243,c_1172]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1939,plain,
% 2.98/1.00      ( r2_hidden(X0,k2_struct_0(sK3)) = iProver_top
% 2.98/1.00      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 2.98/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_1694,c_1529]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1943,plain,
% 2.98/1.00      ( r2_hidden(X0,k2_struct_0(sK3)) = iProver_top
% 2.98/1.00      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 2.98/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1939,c_1177]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_1947,plain,
% 2.98/1.00      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 2.98/1.00      | r2_hidden(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
% 2.98/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_1236,c_1943]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3274,plain,
% 2.98/1.00      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.98/1.00      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
% 2.98/1.00      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(superposition,[status(thm)],[c_3267,c_1947]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3286,plain,
% 2.98/1.00      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.98/1.00      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
% 2.98/1.00      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(light_normalisation,[status(thm)],[c_3274,c_1532]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3296,plain,
% 2.98/1.00      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.98/1.00      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_3293,c_3286]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3808,plain,
% 2.98/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.98/1.00      inference(global_propositional_subsumption,
% 2.98/1.00                [status(thm)],
% 2.98/1.00                [c_1882,c_23,c_1341,c_3296]) ).
% 2.98/1.00  
% 2.98/1.00  cnf(c_3813,plain,
% 2.98/1.00      ( $false ),
% 2.98/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3808,c_1194]) ).
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.98/1.00  
% 2.98/1.00  ------                               Statistics
% 2.98/1.00  
% 2.98/1.00  ------ General
% 2.98/1.00  
% 2.98/1.00  abstr_ref_over_cycles:                  0
% 2.98/1.00  abstr_ref_under_cycles:                 0
% 2.98/1.00  gc_basic_clause_elim:                   0
% 2.98/1.00  forced_gc_time:                         0
% 2.98/1.00  parsing_time:                           0.011
% 2.98/1.00  unif_index_cands_time:                  0.
% 2.98/1.00  unif_index_add_time:                    0.
% 2.98/1.00  orderings_time:                         0.
% 2.98/1.00  out_proof_time:                         0.009
% 2.98/1.00  total_time:                             0.159
% 2.98/1.00  num_of_symbols:                         55
% 2.98/1.00  num_of_terms:                           3259
% 2.98/1.00  
% 2.98/1.00  ------ Preprocessing
% 2.98/1.00  
% 2.98/1.00  num_of_splits:                          0
% 2.98/1.00  num_of_split_atoms:                     0
% 2.98/1.00  num_of_reused_defs:                     0
% 2.98/1.00  num_eq_ax_congr_red:                    41
% 2.98/1.00  num_of_sem_filtered_clauses:            1
% 2.98/1.00  num_of_subtypes:                        0
% 2.98/1.00  monotx_restored_types:                  0
% 2.98/1.00  sat_num_of_epr_types:                   0
% 2.98/1.00  sat_num_of_non_cyclic_types:            0
% 2.98/1.00  sat_guarded_non_collapsed_types:        0
% 2.98/1.00  num_pure_diseq_elim:                    0
% 2.98/1.00  simp_replaced_by:                       0
% 2.98/1.00  res_preprocessed:                       116
% 2.98/1.00  prep_upred:                             0
% 2.98/1.00  prep_unflattend:                        27
% 2.98/1.00  smt_new_axioms:                         0
% 2.98/1.00  pred_elim_cands:                        3
% 2.98/1.00  pred_elim:                              8
% 2.98/1.00  pred_elim_cl:                           9
% 2.98/1.00  pred_elim_cycles:                       11
% 2.98/1.00  merged_defs:                            0
% 2.98/1.00  merged_defs_ncl:                        0
% 2.98/1.00  bin_hyper_res:                          0
% 2.98/1.00  prep_cycles:                            4
% 2.98/1.00  pred_elim_time:                         0.012
% 2.98/1.00  splitting_time:                         0.
% 2.98/1.00  sem_filter_time:                        0.
% 2.98/1.00  monotx_time:                            0.001
% 2.98/1.00  subtype_inf_time:                       0.
% 2.98/1.00  
% 2.98/1.00  ------ Problem properties
% 2.98/1.00  
% 2.98/1.00  clauses:                                20
% 2.98/1.00  conjectures:                            1
% 2.98/1.00  epr:                                    1
% 2.98/1.00  horn:                                   17
% 2.98/1.00  ground:                                 4
% 2.98/1.00  unary:                                  8
% 2.98/1.00  binary:                                 3
% 2.98/1.00  lits:                                   45
% 2.98/1.00  lits_eq:                                12
% 2.98/1.00  fd_pure:                                0
% 2.98/1.00  fd_pseudo:                              0
% 2.98/1.00  fd_cond:                                3
% 2.98/1.00  fd_pseudo_cond:                         0
% 2.98/1.00  ac_symbols:                             0
% 2.98/1.00  
% 2.98/1.00  ------ Propositional Solver
% 2.98/1.00  
% 2.98/1.00  prop_solver_calls:                      29
% 2.98/1.00  prop_fast_solver_calls:                 955
% 2.98/1.00  smt_solver_calls:                       0
% 2.98/1.00  smt_fast_solver_calls:                  0
% 2.98/1.00  prop_num_of_clauses:                    1227
% 2.98/1.00  prop_preprocess_simplified:             4158
% 2.98/1.00  prop_fo_subsumed:                       45
% 2.98/1.00  prop_solver_time:                       0.
% 2.98/1.00  smt_solver_time:                        0.
% 2.98/1.00  smt_fast_solver_time:                   0.
% 2.98/1.00  prop_fast_solver_time:                  0.
% 2.98/1.00  prop_unsat_core_time:                   0.
% 2.98/1.00  
% 2.98/1.00  ------ QBF
% 2.98/1.00  
% 2.98/1.00  qbf_q_res:                              0
% 2.98/1.00  qbf_num_tautologies:                    0
% 2.98/1.00  qbf_prep_cycles:                        0
% 2.98/1.00  
% 2.98/1.00  ------ BMC1
% 2.98/1.00  
% 2.98/1.00  bmc1_current_bound:                     -1
% 2.98/1.00  bmc1_last_solved_bound:                 -1
% 2.98/1.00  bmc1_unsat_core_size:                   -1
% 2.98/1.00  bmc1_unsat_core_parents_size:           -1
% 2.98/1.00  bmc1_merge_next_fun:                    0
% 2.98/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.98/1.00  
% 2.98/1.00  ------ Instantiation
% 2.98/1.00  
% 2.98/1.00  inst_num_of_clauses:                    333
% 2.98/1.00  inst_num_in_passive:                    110
% 2.98/1.00  inst_num_in_active:                     203
% 2.98/1.00  inst_num_in_unprocessed:                20
% 2.98/1.00  inst_num_of_loops:                      240
% 2.98/1.00  inst_num_of_learning_restarts:          0
% 2.98/1.00  inst_num_moves_active_passive:          33
% 2.98/1.00  inst_lit_activity:                      0
% 2.98/1.00  inst_lit_activity_moves:                0
% 2.98/1.00  inst_num_tautologies:                   0
% 2.98/1.00  inst_num_prop_implied:                  0
% 2.98/1.00  inst_num_existing_simplified:           0
% 2.98/1.00  inst_num_eq_res_simplified:             0
% 2.98/1.00  inst_num_child_elim:                    0
% 2.98/1.00  inst_num_of_dismatching_blockings:      107
% 2.98/1.00  inst_num_of_non_proper_insts:           325
% 2.98/1.00  inst_num_of_duplicates:                 0
% 2.98/1.00  inst_inst_num_from_inst_to_res:         0
% 2.98/1.00  inst_dismatching_checking_time:         0.
% 2.98/1.00  
% 2.98/1.00  ------ Resolution
% 2.98/1.00  
% 2.98/1.00  res_num_of_clauses:                     0
% 2.98/1.00  res_num_in_passive:                     0
% 2.98/1.00  res_num_in_active:                      0
% 2.98/1.00  res_num_of_loops:                       120
% 2.98/1.00  res_forward_subset_subsumed:            44
% 2.98/1.00  res_backward_subset_subsumed:           0
% 2.98/1.00  res_forward_subsumed:                   0
% 2.98/1.00  res_backward_subsumed:                  0
% 2.98/1.00  res_forward_subsumption_resolution:     2
% 2.98/1.00  res_backward_subsumption_resolution:    0
% 2.98/1.00  res_clause_to_clause_subsumption:       268
% 2.98/1.00  res_orphan_elimination:                 0
% 2.98/1.00  res_tautology_del:                      25
% 2.98/1.00  res_num_eq_res_simplified:              0
% 2.98/1.00  res_num_sel_changes:                    0
% 2.98/1.00  res_moves_from_active_to_pass:          0
% 2.98/1.00  
% 2.98/1.00  ------ Superposition
% 2.98/1.00  
% 2.98/1.00  sup_time_total:                         0.
% 2.98/1.00  sup_time_generating:                    0.
% 2.98/1.00  sup_time_sim_full:                      0.
% 2.98/1.00  sup_time_sim_immed:                     0.
% 2.98/1.00  
% 2.98/1.00  sup_num_of_clauses:                     81
% 2.98/1.00  sup_num_in_active:                      47
% 2.98/1.00  sup_num_in_passive:                     34
% 2.98/1.00  sup_num_of_loops:                       47
% 2.98/1.00  sup_fw_superposition:                   32
% 2.98/1.00  sup_bw_superposition:                   50
% 2.98/1.00  sup_immediate_simplified:               30
% 2.98/1.00  sup_given_eliminated:                   0
% 2.98/1.00  comparisons_done:                       0
% 2.98/1.00  comparisons_avoided:                    24
% 2.98/1.00  
% 2.98/1.00  ------ Simplifications
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  sim_fw_subset_subsumed:                 6
% 2.98/1.00  sim_bw_subset_subsumed:                 1
% 2.98/1.00  sim_fw_subsumed:                        4
% 2.98/1.00  sim_bw_subsumed:                        1
% 2.98/1.00  sim_fw_subsumption_res:                 5
% 2.98/1.00  sim_bw_subsumption_res:                 1
% 2.98/1.00  sim_tautology_del:                      3
% 2.98/1.00  sim_eq_tautology_del:                   1
% 2.98/1.00  sim_eq_res_simp:                        0
% 2.98/1.00  sim_fw_demodulated:                     2
% 2.98/1.00  sim_bw_demodulated:                     0
% 2.98/1.00  sim_light_normalised:                   31
% 2.98/1.00  sim_joinable_taut:                      0
% 2.98/1.00  sim_joinable_simp:                      0
% 2.98/1.00  sim_ac_normalised:                      0
% 2.98/1.00  sim_smt_subsumption:                    0
% 2.98/1.00  
%------------------------------------------------------------------------------
