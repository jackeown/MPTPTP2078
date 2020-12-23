%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:12 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 786 expanded)
%              Number of clauses        :  104 ( 248 expanded)
%              Number of leaves         :   21 ( 172 expanded)
%              Depth                    :   21
%              Number of atoms          :  667 (3592 expanded)
%              Number of equality atoms :  201 ( 751 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f33])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f40,plain,(
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

fof(f39,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f40,f39])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,
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

fof(f43,plain,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f42])).

fof(f66,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
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

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f43])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_862,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1544,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k2_subset_1(X2) ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_2145,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))
    | X0 != k2_subset_1(X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1544])).

cnf(c_5561,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X1)))
    | ~ m1_subset_1(k2_subset_1(k2_struct_0(X1)),k1_zfmisc_1(k2_struct_0(X1)))
    | X0 != k2_subset_1(k2_struct_0(X1))
    | k1_zfmisc_1(k2_struct_0(X1)) != k1_zfmisc_1(k2_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_2145])).

cnf(c_11043,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3)))
    | ~ m1_subset_1(k2_subset_1(k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3)))
    | k2_struct_0(sK3) != k2_subset_1(k2_struct_0(sK3))
    | k1_zfmisc_1(k2_struct_0(sK3)) != k1_zfmisc_1(k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_5561])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1131,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1132,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1131,c_0])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1127,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_473,plain,
    ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X0,X1,X2) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_474,plain,
    ( ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | sK2(X0,sK3,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_22,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_478,plain,
    ( ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK2(X0,sK3,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_474,c_24,c_23,c_22,c_20])).

cnf(c_1123,plain,
    ( sK2(X0,sK3,X1) = X0
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_12,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_263,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_12,c_6])).

cnf(c_612,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_263,c_20])).

cnf(c_613,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_1136,plain,
    ( sK2(X0,sK3,X1) = X0
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1123,c_613])).

cnf(c_1493,plain,
    ( sK2(sK0(a_2_1_orders_2(sK3,X0)),sK3,X0) = sK0(a_2_1_orders_2(sK3,X0))
    | a_2_1_orders_2(sK3,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1136])).

cnf(c_2526,plain,
    ( sK2(sK0(a_2_1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(a_2_1_orders_2(sK3,k2_struct_0(sK3)))
    | a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1132,c_1493])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_560,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_561,c_24,c_23,c_22,c_20])).

cnf(c_1119,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_1134,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1119,c_613])).

cnf(c_1559,plain,
    ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1132,c_1134])).

cnf(c_2528,plain,
    ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
    | a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2526,c_1559])).

cnf(c_2529,plain,
    ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
    | k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2528,c_1559])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_859,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6965,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_860,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_1305,plain,
    ( k2_orders_2(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k2_orders_2(X0,X1) ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_4593,plain,
    ( k2_orders_2(X0,k2_struct_0(sK3)) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k2_orders_2(X0,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_9335,plain,
    ( k2_orders_2(X0,k2_struct_0(sK3)) != k1_xboole_0
    | k1_xboole_0 = k2_orders_2(X0,k2_struct_0(sK3))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4593])).

cnf(c_9336,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
    | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9335])).

cnf(c_10794,plain,
    ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2529,c_19,c_6965,c_9336])).

cnf(c_16,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_399,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_400,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_404,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_400,c_24,c_23,c_22,c_20])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_420,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_404,c_3])).

cnf(c_1126,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_1140,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1126,c_613])).

cnf(c_8,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_617,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_618,plain,
    ( ~ r2_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_1118,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_1133,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1118,c_613])).

cnf(c_1458,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1140,c_1133])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_452,plain,
    ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_453,plain,
    ( ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_457,plain,
    ( ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_453,c_24,c_23,c_22,c_20])).

cnf(c_1124,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_1137,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1124,c_613])).

cnf(c_2049,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1458,c_1137])).

cnf(c_2050,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2049])).

cnf(c_10799,plain,
    ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10794,c_2050])).

cnf(c_10804,plain,
    ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10799,c_1559])).

cnf(c_10810,plain,
    ( ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
    | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3))
    | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10804])).

cnf(c_8552,plain,
    ( k1_zfmisc_1(k2_struct_0(sK3)) = k1_zfmisc_1(k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_24,c_23,c_22,c_20])).

cnf(c_1120,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_1135,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1120,c_613])).

cnf(c_1129,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2113,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1135,c_1129])).

cnf(c_2351,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_2113])).

cnf(c_3345,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | m1_subset_1(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_2351])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1130,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3618,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3345,c_1130])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1128,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1722,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1135,c_1128])).

cnf(c_1951,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1722])).

cnf(c_2785,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1951])).

cnf(c_6083,plain,
    ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
    | k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3618,c_2785])).

cnf(c_6084,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6083])).

cnf(c_6085,plain,
    ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3))
    | k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6084])).

cnf(c_5208,plain,
    ( m1_subset_1(k2_subset_1(k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1936,plain,
    ( X0 != X1
    | k2_struct_0(sK3) != X1
    | k2_struct_0(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_2864,plain,
    ( X0 != k2_struct_0(sK3)
    | k2_struct_0(sK3) = X0
    | k2_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1936])).

cnf(c_4240,plain,
    ( k2_struct_0(sK3) != k2_struct_0(sK3)
    | k2_struct_0(sK3) = k2_subset_1(k2_struct_0(sK3))
    | k2_subset_1(k2_struct_0(sK3)) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2864])).

cnf(c_1856,plain,
    ( k2_subset_1(k2_struct_0(sK3)) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1185,plain,
    ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
    | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_882,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_864,plain,
    ( X0 != X1
    | k2_struct_0(X0) = k2_struct_0(X1) ),
    theory(equality)).

cnf(c_874,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11043,c_10810,c_9336,c_8552,c_6965,c_6085,c_5208,c_4240,c_1856,c_1185,c_882,c_874,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.55/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.01  
% 3.55/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.55/1.01  
% 3.55/1.01  ------  iProver source info
% 3.55/1.01  
% 3.55/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.55/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.55/1.01  git: non_committed_changes: false
% 3.55/1.01  git: last_make_outside_of_git: false
% 3.55/1.01  
% 3.55/1.01  ------ 
% 3.55/1.01  
% 3.55/1.01  ------ Input Options
% 3.55/1.01  
% 3.55/1.01  --out_options                           all
% 3.55/1.01  --tptp_safe_out                         true
% 3.55/1.01  --problem_path                          ""
% 3.55/1.01  --include_path                          ""
% 3.55/1.01  --clausifier                            res/vclausify_rel
% 3.55/1.01  --clausifier_options                    ""
% 3.55/1.01  --stdin                                 false
% 3.55/1.01  --stats_out                             all
% 3.55/1.01  
% 3.55/1.01  ------ General Options
% 3.55/1.01  
% 3.55/1.01  --fof                                   false
% 3.55/1.01  --time_out_real                         305.
% 3.55/1.01  --time_out_virtual                      -1.
% 3.55/1.01  --symbol_type_check                     false
% 3.55/1.01  --clausify_out                          false
% 3.55/1.01  --sig_cnt_out                           false
% 3.55/1.01  --trig_cnt_out                          false
% 3.55/1.01  --trig_cnt_out_tolerance                1.
% 3.55/1.01  --trig_cnt_out_sk_spl                   false
% 3.55/1.01  --abstr_cl_out                          false
% 3.55/1.01  
% 3.55/1.01  ------ Global Options
% 3.55/1.01  
% 3.55/1.01  --schedule                              default
% 3.55/1.01  --add_important_lit                     false
% 3.55/1.01  --prop_solver_per_cl                    1000
% 3.55/1.01  --min_unsat_core                        false
% 3.55/1.01  --soft_assumptions                      false
% 3.55/1.01  --soft_lemma_size                       3
% 3.55/1.01  --prop_impl_unit_size                   0
% 3.55/1.01  --prop_impl_unit                        []
% 3.55/1.01  --share_sel_clauses                     true
% 3.55/1.01  --reset_solvers                         false
% 3.55/1.01  --bc_imp_inh                            [conj_cone]
% 3.55/1.01  --conj_cone_tolerance                   3.
% 3.55/1.01  --extra_neg_conj                        none
% 3.55/1.01  --large_theory_mode                     true
% 3.55/1.01  --prolific_symb_bound                   200
% 3.55/1.01  --lt_threshold                          2000
% 3.55/1.01  --clause_weak_htbl                      true
% 3.55/1.01  --gc_record_bc_elim                     false
% 3.55/1.01  
% 3.55/1.01  ------ Preprocessing Options
% 3.55/1.01  
% 3.55/1.01  --preprocessing_flag                    true
% 3.55/1.01  --time_out_prep_mult                    0.1
% 3.55/1.01  --splitting_mode                        input
% 3.55/1.01  --splitting_grd                         true
% 3.55/1.01  --splitting_cvd                         false
% 3.55/1.01  --splitting_cvd_svl                     false
% 3.55/1.01  --splitting_nvd                         32
% 3.55/1.01  --sub_typing                            true
% 3.55/1.01  --prep_gs_sim                           true
% 3.55/1.01  --prep_unflatten                        true
% 3.55/1.01  --prep_res_sim                          true
% 3.55/1.01  --prep_upred                            true
% 3.55/1.01  --prep_sem_filter                       exhaustive
% 3.55/1.01  --prep_sem_filter_out                   false
% 3.55/1.01  --pred_elim                             true
% 3.55/1.01  --res_sim_input                         true
% 3.55/1.01  --eq_ax_congr_red                       true
% 3.55/1.01  --pure_diseq_elim                       true
% 3.55/1.01  --brand_transform                       false
% 3.55/1.01  --non_eq_to_eq                          false
% 3.55/1.01  --prep_def_merge                        true
% 3.55/1.01  --prep_def_merge_prop_impl              false
% 3.55/1.01  --prep_def_merge_mbd                    true
% 3.55/1.01  --prep_def_merge_tr_red                 false
% 3.55/1.01  --prep_def_merge_tr_cl                  false
% 3.55/1.01  --smt_preprocessing                     true
% 3.55/1.01  --smt_ac_axioms                         fast
% 3.55/1.01  --preprocessed_out                      false
% 3.55/1.01  --preprocessed_stats                    false
% 3.55/1.01  
% 3.55/1.01  ------ Abstraction refinement Options
% 3.55/1.01  
% 3.55/1.01  --abstr_ref                             []
% 3.55/1.01  --abstr_ref_prep                        false
% 3.55/1.01  --abstr_ref_until_sat                   false
% 3.55/1.01  --abstr_ref_sig_restrict                funpre
% 3.55/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/1.01  --abstr_ref_under                       []
% 3.55/1.01  
% 3.55/1.01  ------ SAT Options
% 3.55/1.01  
% 3.55/1.01  --sat_mode                              false
% 3.55/1.01  --sat_fm_restart_options                ""
% 3.55/1.01  --sat_gr_def                            false
% 3.55/1.01  --sat_epr_types                         true
% 3.55/1.01  --sat_non_cyclic_types                  false
% 3.55/1.01  --sat_finite_models                     false
% 3.55/1.01  --sat_fm_lemmas                         false
% 3.55/1.01  --sat_fm_prep                           false
% 3.55/1.01  --sat_fm_uc_incr                        true
% 3.55/1.01  --sat_out_model                         small
% 3.55/1.01  --sat_out_clauses                       false
% 3.55/1.01  
% 3.55/1.01  ------ QBF Options
% 3.55/1.01  
% 3.55/1.01  --qbf_mode                              false
% 3.55/1.01  --qbf_elim_univ                         false
% 3.55/1.01  --qbf_dom_inst                          none
% 3.55/1.01  --qbf_dom_pre_inst                      false
% 3.55/1.01  --qbf_sk_in                             false
% 3.55/1.01  --qbf_pred_elim                         true
% 3.55/1.01  --qbf_split                             512
% 3.55/1.01  
% 3.55/1.01  ------ BMC1 Options
% 3.55/1.01  
% 3.55/1.01  --bmc1_incremental                      false
% 3.55/1.01  --bmc1_axioms                           reachable_all
% 3.55/1.01  --bmc1_min_bound                        0
% 3.55/1.01  --bmc1_max_bound                        -1
% 3.55/1.01  --bmc1_max_bound_default                -1
% 3.55/1.01  --bmc1_symbol_reachability              true
% 3.55/1.01  --bmc1_property_lemmas                  false
% 3.55/1.01  --bmc1_k_induction                      false
% 3.55/1.01  --bmc1_non_equiv_states                 false
% 3.55/1.01  --bmc1_deadlock                         false
% 3.55/1.01  --bmc1_ucm                              false
% 3.55/1.01  --bmc1_add_unsat_core                   none
% 3.55/1.01  --bmc1_unsat_core_children              false
% 3.55/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/1.01  --bmc1_out_stat                         full
% 3.55/1.01  --bmc1_ground_init                      false
% 3.55/1.01  --bmc1_pre_inst_next_state              false
% 3.55/1.01  --bmc1_pre_inst_state                   false
% 3.55/1.01  --bmc1_pre_inst_reach_state             false
% 3.55/1.01  --bmc1_out_unsat_core                   false
% 3.55/1.01  --bmc1_aig_witness_out                  false
% 3.55/1.01  --bmc1_verbose                          false
% 3.55/1.01  --bmc1_dump_clauses_tptp                false
% 3.55/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.55/1.01  --bmc1_dump_file                        -
% 3.55/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.55/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.55/1.01  --bmc1_ucm_extend_mode                  1
% 3.55/1.01  --bmc1_ucm_init_mode                    2
% 3.55/1.01  --bmc1_ucm_cone_mode                    none
% 3.55/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.55/1.01  --bmc1_ucm_relax_model                  4
% 3.55/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.55/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/1.01  --bmc1_ucm_layered_model                none
% 3.55/1.01  --bmc1_ucm_max_lemma_size               10
% 3.55/1.01  
% 3.55/1.01  ------ AIG Options
% 3.55/1.01  
% 3.55/1.01  --aig_mode                              false
% 3.55/1.01  
% 3.55/1.01  ------ Instantiation Options
% 3.55/1.01  
% 3.55/1.01  --instantiation_flag                    true
% 3.55/1.01  --inst_sos_flag                         true
% 3.55/1.01  --inst_sos_phase                        true
% 3.55/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/1.01  --inst_lit_sel_side                     num_symb
% 3.55/1.01  --inst_solver_per_active                1400
% 3.55/1.01  --inst_solver_calls_frac                1.
% 3.55/1.01  --inst_passive_queue_type               priority_queues
% 3.55/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/1.01  --inst_passive_queues_freq              [25;2]
% 3.55/1.01  --inst_dismatching                      true
% 3.55/1.01  --inst_eager_unprocessed_to_passive     true
% 3.55/1.01  --inst_prop_sim_given                   true
% 3.55/1.01  --inst_prop_sim_new                     false
% 3.55/1.01  --inst_subs_new                         false
% 3.55/1.01  --inst_eq_res_simp                      false
% 3.55/1.01  --inst_subs_given                       false
% 3.55/1.01  --inst_orphan_elimination               true
% 3.55/1.01  --inst_learning_loop_flag               true
% 3.55/1.01  --inst_learning_start                   3000
% 3.55/1.01  --inst_learning_factor                  2
% 3.55/1.01  --inst_start_prop_sim_after_learn       3
% 3.55/1.01  --inst_sel_renew                        solver
% 3.55/1.01  --inst_lit_activity_flag                true
% 3.55/1.01  --inst_restr_to_given                   false
% 3.55/1.01  --inst_activity_threshold               500
% 3.55/1.01  --inst_out_proof                        true
% 3.55/1.01  
% 3.55/1.01  ------ Resolution Options
% 3.55/1.01  
% 3.55/1.01  --resolution_flag                       true
% 3.55/1.01  --res_lit_sel                           adaptive
% 3.55/1.01  --res_lit_sel_side                      none
% 3.55/1.01  --res_ordering                          kbo
% 3.55/1.01  --res_to_prop_solver                    active
% 3.55/1.01  --res_prop_simpl_new                    false
% 3.55/1.01  --res_prop_simpl_given                  true
% 3.55/1.01  --res_passive_queue_type                priority_queues
% 3.55/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/1.01  --res_passive_queues_freq               [15;5]
% 3.55/1.01  --res_forward_subs                      full
% 3.55/1.01  --res_backward_subs                     full
% 3.55/1.01  --res_forward_subs_resolution           true
% 3.55/1.01  --res_backward_subs_resolution          true
% 3.55/1.01  --res_orphan_elimination                true
% 3.55/1.01  --res_time_limit                        2.
% 3.55/1.01  --res_out_proof                         true
% 3.55/1.01  
% 3.55/1.01  ------ Superposition Options
% 3.55/1.01  
% 3.55/1.01  --superposition_flag                    true
% 3.55/1.01  --sup_passive_queue_type                priority_queues
% 3.55/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.55/1.01  --demod_completeness_check              fast
% 3.55/1.01  --demod_use_ground                      true
% 3.55/1.01  --sup_to_prop_solver                    passive
% 3.55/1.01  --sup_prop_simpl_new                    true
% 3.55/1.01  --sup_prop_simpl_given                  true
% 3.55/1.01  --sup_fun_splitting                     true
% 3.55/1.01  --sup_smt_interval                      50000
% 3.55/1.01  
% 3.55/1.01  ------ Superposition Simplification Setup
% 3.55/1.01  
% 3.55/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.55/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.55/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.55/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.55/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.55/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.55/1.01  --sup_immed_triv                        [TrivRules]
% 3.55/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.01  --sup_immed_bw_main                     []
% 3.55/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.55/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.01  --sup_input_bw                          []
% 3.55/1.01  
% 3.55/1.01  ------ Combination Options
% 3.55/1.01  
% 3.55/1.01  --comb_res_mult                         3
% 3.55/1.01  --comb_sup_mult                         2
% 3.55/1.01  --comb_inst_mult                        10
% 3.55/1.01  
% 3.55/1.01  ------ Debug Options
% 3.55/1.01  
% 3.55/1.01  --dbg_backtrace                         false
% 3.55/1.01  --dbg_dump_prop_clauses                 false
% 3.55/1.01  --dbg_dump_prop_clauses_file            -
% 3.55/1.01  --dbg_out_stat                          false
% 3.55/1.01  ------ Parsing...
% 3.55/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.55/1.01  
% 3.55/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.55/1.01  
% 3.55/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.55/1.01  
% 3.55/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.55/1.01  ------ Proving...
% 3.55/1.01  ------ Problem Properties 
% 3.55/1.01  
% 3.55/1.01  
% 3.55/1.01  clauses                                 17
% 3.55/1.01  conjectures                             1
% 3.55/1.01  EPR                                     1
% 3.55/1.01  Horn                                    13
% 3.55/1.01  unary                                   4
% 3.55/1.01  binary                                  4
% 3.55/1.01  lits                                    43
% 3.55/1.01  lits eq                                 6
% 3.55/1.01  fd_pure                                 0
% 3.55/1.01  fd_pseudo                               0
% 3.55/1.01  fd_cond                                 1
% 3.55/1.01  fd_pseudo_cond                          0
% 3.55/1.01  AC symbols                              0
% 3.55/1.01  
% 3.55/1.01  ------ Schedule dynamic 5 is on 
% 3.55/1.01  
% 3.55/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.55/1.01  
% 3.55/1.01  
% 3.55/1.01  ------ 
% 3.55/1.01  Current options:
% 3.55/1.01  ------ 
% 3.55/1.01  
% 3.55/1.01  ------ Input Options
% 3.55/1.01  
% 3.55/1.01  --out_options                           all
% 3.55/1.01  --tptp_safe_out                         true
% 3.55/1.01  --problem_path                          ""
% 3.55/1.01  --include_path                          ""
% 3.55/1.01  --clausifier                            res/vclausify_rel
% 3.55/1.01  --clausifier_options                    ""
% 3.55/1.01  --stdin                                 false
% 3.55/1.01  --stats_out                             all
% 3.55/1.01  
% 3.55/1.01  ------ General Options
% 3.55/1.01  
% 3.55/1.01  --fof                                   false
% 3.55/1.01  --time_out_real                         305.
% 3.55/1.01  --time_out_virtual                      -1.
% 3.55/1.01  --symbol_type_check                     false
% 3.55/1.01  --clausify_out                          false
% 3.55/1.01  --sig_cnt_out                           false
% 3.55/1.01  --trig_cnt_out                          false
% 3.55/1.01  --trig_cnt_out_tolerance                1.
% 3.55/1.01  --trig_cnt_out_sk_spl                   false
% 3.55/1.01  --abstr_cl_out                          false
% 3.55/1.01  
% 3.55/1.01  ------ Global Options
% 3.55/1.01  
% 3.55/1.01  --schedule                              default
% 3.55/1.01  --add_important_lit                     false
% 3.55/1.01  --prop_solver_per_cl                    1000
% 3.55/1.01  --min_unsat_core                        false
% 3.55/1.01  --soft_assumptions                      false
% 3.55/1.01  --soft_lemma_size                       3
% 3.55/1.01  --prop_impl_unit_size                   0
% 3.55/1.01  --prop_impl_unit                        []
% 3.55/1.01  --share_sel_clauses                     true
% 3.55/1.01  --reset_solvers                         false
% 3.55/1.01  --bc_imp_inh                            [conj_cone]
% 3.55/1.01  --conj_cone_tolerance                   3.
% 3.55/1.01  --extra_neg_conj                        none
% 3.55/1.01  --large_theory_mode                     true
% 3.55/1.01  --prolific_symb_bound                   200
% 3.55/1.01  --lt_threshold                          2000
% 3.55/1.01  --clause_weak_htbl                      true
% 3.55/1.01  --gc_record_bc_elim                     false
% 3.55/1.01  
% 3.55/1.01  ------ Preprocessing Options
% 3.55/1.01  
% 3.55/1.01  --preprocessing_flag                    true
% 3.55/1.01  --time_out_prep_mult                    0.1
% 3.55/1.01  --splitting_mode                        input
% 3.55/1.01  --splitting_grd                         true
% 3.55/1.01  --splitting_cvd                         false
% 3.55/1.01  --splitting_cvd_svl                     false
% 3.55/1.01  --splitting_nvd                         32
% 3.55/1.01  --sub_typing                            true
% 3.55/1.01  --prep_gs_sim                           true
% 3.55/1.01  --prep_unflatten                        true
% 3.55/1.01  --prep_res_sim                          true
% 3.55/1.01  --prep_upred                            true
% 3.55/1.01  --prep_sem_filter                       exhaustive
% 3.55/1.01  --prep_sem_filter_out                   false
% 3.55/1.01  --pred_elim                             true
% 3.55/1.01  --res_sim_input                         true
% 3.55/1.01  --eq_ax_congr_red                       true
% 3.55/1.01  --pure_diseq_elim                       true
% 3.55/1.01  --brand_transform                       false
% 3.55/1.01  --non_eq_to_eq                          false
% 3.55/1.01  --prep_def_merge                        true
% 3.55/1.01  --prep_def_merge_prop_impl              false
% 3.55/1.01  --prep_def_merge_mbd                    true
% 3.55/1.01  --prep_def_merge_tr_red                 false
% 3.55/1.01  --prep_def_merge_tr_cl                  false
% 3.55/1.01  --smt_preprocessing                     true
% 3.55/1.01  --smt_ac_axioms                         fast
% 3.55/1.01  --preprocessed_out                      false
% 3.55/1.01  --preprocessed_stats                    false
% 3.55/1.01  
% 3.55/1.01  ------ Abstraction refinement Options
% 3.55/1.01  
% 3.55/1.01  --abstr_ref                             []
% 3.55/1.01  --abstr_ref_prep                        false
% 3.55/1.01  --abstr_ref_until_sat                   false
% 3.55/1.01  --abstr_ref_sig_restrict                funpre
% 3.55/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/1.01  --abstr_ref_under                       []
% 3.55/1.01  
% 3.55/1.01  ------ SAT Options
% 3.55/1.01  
% 3.55/1.01  --sat_mode                              false
% 3.55/1.01  --sat_fm_restart_options                ""
% 3.55/1.01  --sat_gr_def                            false
% 3.55/1.01  --sat_epr_types                         true
% 3.55/1.01  --sat_non_cyclic_types                  false
% 3.55/1.01  --sat_finite_models                     false
% 3.55/1.01  --sat_fm_lemmas                         false
% 3.55/1.01  --sat_fm_prep                           false
% 3.55/1.01  --sat_fm_uc_incr                        true
% 3.55/1.01  --sat_out_model                         small
% 3.55/1.01  --sat_out_clauses                       false
% 3.55/1.01  
% 3.55/1.01  ------ QBF Options
% 3.55/1.01  
% 3.55/1.01  --qbf_mode                              false
% 3.55/1.01  --qbf_elim_univ                         false
% 3.55/1.01  --qbf_dom_inst                          none
% 3.55/1.01  --qbf_dom_pre_inst                      false
% 3.55/1.01  --qbf_sk_in                             false
% 3.55/1.01  --qbf_pred_elim                         true
% 3.55/1.01  --qbf_split                             512
% 3.55/1.01  
% 3.55/1.01  ------ BMC1 Options
% 3.55/1.01  
% 3.55/1.01  --bmc1_incremental                      false
% 3.55/1.01  --bmc1_axioms                           reachable_all
% 3.55/1.01  --bmc1_min_bound                        0
% 3.55/1.01  --bmc1_max_bound                        -1
% 3.55/1.01  --bmc1_max_bound_default                -1
% 3.55/1.01  --bmc1_symbol_reachability              true
% 3.55/1.01  --bmc1_property_lemmas                  false
% 3.55/1.01  --bmc1_k_induction                      false
% 3.55/1.01  --bmc1_non_equiv_states                 false
% 3.55/1.01  --bmc1_deadlock                         false
% 3.55/1.01  --bmc1_ucm                              false
% 3.55/1.01  --bmc1_add_unsat_core                   none
% 3.55/1.01  --bmc1_unsat_core_children              false
% 3.55/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/1.01  --bmc1_out_stat                         full
% 3.55/1.01  --bmc1_ground_init                      false
% 3.55/1.01  --bmc1_pre_inst_next_state              false
% 3.55/1.01  --bmc1_pre_inst_state                   false
% 3.55/1.01  --bmc1_pre_inst_reach_state             false
% 3.55/1.01  --bmc1_out_unsat_core                   false
% 3.55/1.01  --bmc1_aig_witness_out                  false
% 3.55/1.01  --bmc1_verbose                          false
% 3.55/1.01  --bmc1_dump_clauses_tptp                false
% 3.55/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.55/1.01  --bmc1_dump_file                        -
% 3.55/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.55/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.55/1.01  --bmc1_ucm_extend_mode                  1
% 3.55/1.01  --bmc1_ucm_init_mode                    2
% 3.55/1.01  --bmc1_ucm_cone_mode                    none
% 3.55/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.55/1.01  --bmc1_ucm_relax_model                  4
% 3.55/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.55/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/1.01  --bmc1_ucm_layered_model                none
% 3.55/1.01  --bmc1_ucm_max_lemma_size               10
% 3.55/1.01  
% 3.55/1.01  ------ AIG Options
% 3.55/1.01  
% 3.55/1.01  --aig_mode                              false
% 3.55/1.01  
% 3.55/1.01  ------ Instantiation Options
% 3.55/1.01  
% 3.55/1.01  --instantiation_flag                    true
% 3.55/1.01  --inst_sos_flag                         true
% 3.55/1.01  --inst_sos_phase                        true
% 3.55/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/1.01  --inst_lit_sel_side                     none
% 3.55/1.01  --inst_solver_per_active                1400
% 3.55/1.01  --inst_solver_calls_frac                1.
% 3.55/1.01  --inst_passive_queue_type               priority_queues
% 3.55/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/1.01  --inst_passive_queues_freq              [25;2]
% 3.55/1.01  --inst_dismatching                      true
% 3.55/1.01  --inst_eager_unprocessed_to_passive     true
% 3.55/1.01  --inst_prop_sim_given                   true
% 3.55/1.01  --inst_prop_sim_new                     false
% 3.55/1.01  --inst_subs_new                         false
% 3.55/1.01  --inst_eq_res_simp                      false
% 3.55/1.01  --inst_subs_given                       false
% 3.55/1.01  --inst_orphan_elimination               true
% 3.55/1.01  --inst_learning_loop_flag               true
% 3.55/1.01  --inst_learning_start                   3000
% 3.55/1.01  --inst_learning_factor                  2
% 3.55/1.01  --inst_start_prop_sim_after_learn       3
% 3.55/1.01  --inst_sel_renew                        solver
% 3.55/1.01  --inst_lit_activity_flag                true
% 3.55/1.01  --inst_restr_to_given                   false
% 3.55/1.01  --inst_activity_threshold               500
% 3.55/1.01  --inst_out_proof                        true
% 3.55/1.01  
% 3.55/1.01  ------ Resolution Options
% 3.55/1.01  
% 3.55/1.01  --resolution_flag                       false
% 3.55/1.01  --res_lit_sel                           adaptive
% 3.55/1.01  --res_lit_sel_side                      none
% 3.55/1.01  --res_ordering                          kbo
% 3.55/1.01  --res_to_prop_solver                    active
% 3.55/1.01  --res_prop_simpl_new                    false
% 3.55/1.01  --res_prop_simpl_given                  true
% 3.55/1.01  --res_passive_queue_type                priority_queues
% 3.55/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/1.01  --res_passive_queues_freq               [15;5]
% 3.55/1.01  --res_forward_subs                      full
% 3.55/1.01  --res_backward_subs                     full
% 3.55/1.01  --res_forward_subs_resolution           true
% 3.55/1.01  --res_backward_subs_resolution          true
% 3.55/1.01  --res_orphan_elimination                true
% 3.55/1.01  --res_time_limit                        2.
% 3.55/1.01  --res_out_proof                         true
% 3.55/1.01  
% 3.55/1.01  ------ Superposition Options
% 3.55/1.01  
% 3.55/1.01  --superposition_flag                    true
% 3.55/1.01  --sup_passive_queue_type                priority_queues
% 3.55/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.55/1.01  --demod_completeness_check              fast
% 3.55/1.01  --demod_use_ground                      true
% 3.55/1.01  --sup_to_prop_solver                    passive
% 3.55/1.01  --sup_prop_simpl_new                    true
% 3.55/1.01  --sup_prop_simpl_given                  true
% 3.55/1.01  --sup_fun_splitting                     true
% 3.55/1.01  --sup_smt_interval                      50000
% 3.55/1.01  
% 3.55/1.01  ------ Superposition Simplification Setup
% 3.55/1.01  
% 3.55/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.55/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.55/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.55/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.55/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.55/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.55/1.01  --sup_immed_triv                        [TrivRules]
% 3.55/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.01  --sup_immed_bw_main                     []
% 3.55/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.55/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.01  --sup_input_bw                          []
% 3.55/1.01  
% 3.55/1.01  ------ Combination Options
% 3.55/1.01  
% 3.55/1.01  --comb_res_mult                         3
% 3.55/1.01  --comb_sup_mult                         2
% 3.55/1.01  --comb_inst_mult                        10
% 3.55/1.01  
% 3.55/1.01  ------ Debug Options
% 3.55/1.01  
% 3.55/1.01  --dbg_backtrace                         false
% 3.55/1.01  --dbg_dump_prop_clauses                 false
% 3.55/1.01  --dbg_dump_prop_clauses_file            -
% 3.55/1.01  --dbg_out_stat                          false
% 3.55/1.01  
% 3.55/1.01  
% 3.55/1.01  
% 3.55/1.01  
% 3.55/1.01  ------ Proving...
% 3.55/1.01  
% 3.55/1.01  
% 3.55/1.01  % SZS status Theorem for theBenchmark.p
% 3.55/1.01  
% 3.55/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.55/1.01  
% 3.55/1.01  fof(f2,axiom,(
% 3.55/1.01    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.55/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f45,plain,(
% 3.55/1.01    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.55/1.01    inference(cnf_transformation,[],[f2])).
% 3.55/1.01  
% 3.55/1.01  fof(f1,axiom,(
% 3.55/1.01    ! [X0] : k2_subset_1(X0) = X0),
% 3.55/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f44,plain,(
% 3.55/1.01    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.55/1.01    inference(cnf_transformation,[],[f1])).
% 3.55/1.01  
% 3.55/1.01  fof(f6,axiom,(
% 3.55/1.01    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.55/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f15,plain,(
% 3.55/1.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.55/1.01    inference(pure_predicate_removal,[],[f6])).
% 3.55/1.01  
% 3.55/1.01  fof(f21,plain,(
% 3.55/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.55/1.01    inference(ennf_transformation,[],[f15])).
% 3.55/1.01  
% 3.55/1.01  fof(f33,plain,(
% 3.55/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.55/1.01    introduced(choice_axiom,[])).
% 3.55/1.01  
% 3.55/1.01  fof(f34,plain,(
% 3.55/1.01    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 3.55/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f33])).
% 3.55/1.01  
% 3.55/1.01  fof(f49,plain,(
% 3.55/1.01    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.55/1.01    inference(cnf_transformation,[],[f34])).
% 3.55/1.01  
% 3.55/1.01  fof(f12,axiom,(
% 3.55/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.55/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f29,plain,(
% 3.55/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 3.55/1.01    inference(ennf_transformation,[],[f12])).
% 3.55/1.01  
% 3.55/1.01  fof(f30,plain,(
% 3.55/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.55/1.01    inference(flattening,[],[f29])).
% 3.55/1.01  
% 3.55/1.01  fof(f37,plain,(
% 3.55/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.55/1.01    inference(nnf_transformation,[],[f30])).
% 3.55/1.01  
% 3.55/1.01  fof(f38,plain,(
% 3.55/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.55/1.01    inference(rectify,[],[f37])).
% 3.55/1.01  
% 3.55/1.01  fof(f40,plain,(
% 3.55/1.01    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.55/1.01    introduced(choice_axiom,[])).
% 3.55/1.01  
% 3.55/1.01  fof(f39,plain,(
% 3.55/1.01    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 3.55/1.01    introduced(choice_axiom,[])).
% 3.55/1.01  
% 3.55/1.01  fof(f41,plain,(
% 3.55/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.55/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f40,f39])).
% 3.55/1.01  
% 3.55/1.01  fof(f58,plain,(
% 3.55/1.01    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f41])).
% 3.55/1.01  
% 3.55/1.01  fof(f13,conjecture,(
% 3.55/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 3.55/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f14,negated_conjecture,(
% 3.55/1.01    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 3.55/1.01    inference(negated_conjecture,[],[f13])).
% 3.55/1.01  
% 3.55/1.01  fof(f31,plain,(
% 3.55/1.01    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.55/1.01    inference(ennf_transformation,[],[f14])).
% 3.55/1.01  
% 3.55/1.01  fof(f32,plain,(
% 3.55/1.01    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.55/1.01    inference(flattening,[],[f31])).
% 3.55/1.01  
% 3.55/1.01  fof(f42,plain,(
% 3.55/1.01    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 3.55/1.01    introduced(choice_axiom,[])).
% 3.55/1.01  
% 3.55/1.01  fof(f43,plain,(
% 3.55/1.01    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 3.55/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f42])).
% 3.55/1.01  
% 3.55/1.01  fof(f66,plain,(
% 3.55/1.01    v5_orders_2(sK3)),
% 3.55/1.01    inference(cnf_transformation,[],[f43])).
% 3.55/1.01  
% 3.55/1.01  fof(f63,plain,(
% 3.55/1.01    ~v2_struct_0(sK3)),
% 3.55/1.01    inference(cnf_transformation,[],[f43])).
% 3.55/1.01  
% 3.55/1.01  fof(f64,plain,(
% 3.55/1.01    v3_orders_2(sK3)),
% 3.55/1.01    inference(cnf_transformation,[],[f43])).
% 3.55/1.01  
% 3.55/1.01  fof(f65,plain,(
% 3.55/1.01    v4_orders_2(sK3)),
% 3.55/1.01    inference(cnf_transformation,[],[f43])).
% 3.55/1.01  
% 3.55/1.01  fof(f67,plain,(
% 3.55/1.01    l1_orders_2(sK3)),
% 3.55/1.01    inference(cnf_transformation,[],[f43])).
% 3.55/1.01  
% 3.55/1.01  fof(f11,axiom,(
% 3.55/1.01    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.55/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f28,plain,(
% 3.55/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.55/1.01    inference(ennf_transformation,[],[f11])).
% 3.55/1.01  
% 3.55/1.01  fof(f56,plain,(
% 3.55/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f28])).
% 3.55/1.01  
% 3.55/1.01  fof(f7,axiom,(
% 3.55/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.55/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f22,plain,(
% 3.55/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.55/1.01    inference(ennf_transformation,[],[f7])).
% 3.55/1.01  
% 3.55/1.01  fof(f50,plain,(
% 3.55/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f22])).
% 3.55/1.01  
% 3.55/1.01  fof(f9,axiom,(
% 3.55/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 3.55/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f24,plain,(
% 3.55/1.01    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.55/1.01    inference(ennf_transformation,[],[f9])).
% 3.55/1.01  
% 3.55/1.01  fof(f25,plain,(
% 3.55/1.01    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.55/1.01    inference(flattening,[],[f24])).
% 3.55/1.01  
% 3.55/1.01  fof(f54,plain,(
% 3.55/1.01    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f25])).
% 3.55/1.01  
% 3.55/1.01  fof(f68,plain,(
% 3.55/1.01    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))),
% 3.55/1.01    inference(cnf_transformation,[],[f43])).
% 3.55/1.01  
% 3.55/1.01  fof(f59,plain,(
% 3.55/1.01    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f41])).
% 3.55/1.01  
% 3.55/1.01  fof(f4,axiom,(
% 3.55/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.55/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f18,plain,(
% 3.55/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.55/1.01    inference(ennf_transformation,[],[f4])).
% 3.55/1.01  
% 3.55/1.01  fof(f19,plain,(
% 3.55/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.55/1.01    inference(flattening,[],[f18])).
% 3.55/1.01  
% 3.55/1.01  fof(f47,plain,(
% 3.55/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f19])).
% 3.55/1.01  
% 3.55/1.01  fof(f8,axiom,(
% 3.55/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 3.55/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f23,plain,(
% 3.55/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.55/1.01    inference(ennf_transformation,[],[f8])).
% 3.55/1.01  
% 3.55/1.01  fof(f35,plain,(
% 3.55/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.55/1.01    inference(nnf_transformation,[],[f23])).
% 3.55/1.01  
% 3.55/1.01  fof(f36,plain,(
% 3.55/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.55/1.01    inference(flattening,[],[f35])).
% 3.55/1.01  
% 3.55/1.01  fof(f52,plain,(
% 3.55/1.01    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f36])).
% 3.55/1.01  
% 3.55/1.01  fof(f69,plain,(
% 3.55/1.01    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.55/1.01    inference(equality_resolution,[],[f52])).
% 3.55/1.01  
% 3.55/1.01  fof(f57,plain,(
% 3.55/1.01    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f41])).
% 3.55/1.01  
% 3.55/1.01  fof(f10,axiom,(
% 3.55/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.55/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f26,plain,(
% 3.55/1.01    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.55/1.01    inference(ennf_transformation,[],[f10])).
% 3.55/1.01  
% 3.55/1.01  fof(f27,plain,(
% 3.55/1.01    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.55/1.01    inference(flattening,[],[f26])).
% 3.55/1.01  
% 3.55/1.01  fof(f55,plain,(
% 3.55/1.01    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f27])).
% 3.55/1.01  
% 3.55/1.01  fof(f3,axiom,(
% 3.55/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.55/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f16,plain,(
% 3.55/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.55/1.01    inference(ennf_transformation,[],[f3])).
% 3.55/1.01  
% 3.55/1.01  fof(f17,plain,(
% 3.55/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.55/1.01    inference(flattening,[],[f16])).
% 3.55/1.01  
% 3.55/1.01  fof(f46,plain,(
% 3.55/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f17])).
% 3.55/1.01  
% 3.55/1.01  fof(f5,axiom,(
% 3.55/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.55/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.01  
% 3.55/1.01  fof(f20,plain,(
% 3.55/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.55/1.01    inference(ennf_transformation,[],[f5])).
% 3.55/1.01  
% 3.55/1.01  fof(f48,plain,(
% 3.55/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.55/1.01    inference(cnf_transformation,[],[f20])).
% 3.55/1.01  
% 3.55/1.01  cnf(c_862,plain,
% 3.55/1.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.55/1.01      theory(equality) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1544,plain,
% 3.55/1.01      ( m1_subset_1(X0,X1)
% 3.55/1.01      | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X2))
% 3.55/1.01      | X1 != k1_zfmisc_1(X2)
% 3.55/1.01      | X0 != k2_subset_1(X2) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_862]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2145,plain,
% 3.55/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.55/1.01      | ~ m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))
% 3.55/1.01      | X0 != k2_subset_1(X1)
% 3.55/1.01      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_1544]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_5561,plain,
% 3.55/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X1)))
% 3.55/1.01      | ~ m1_subset_1(k2_subset_1(k2_struct_0(X1)),k1_zfmisc_1(k2_struct_0(X1)))
% 3.55/1.01      | X0 != k2_subset_1(k2_struct_0(X1))
% 3.55/1.01      | k1_zfmisc_1(k2_struct_0(X1)) != k1_zfmisc_1(k2_struct_0(X1)) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_2145]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_11043,plain,
% 3.55/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3)))
% 3.55/1.01      | ~ m1_subset_1(k2_subset_1(k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3)))
% 3.55/1.01      | k2_struct_0(sK3) != k2_subset_1(k2_struct_0(sK3))
% 3.55/1.01      | k1_zfmisc_1(k2_struct_0(sK3)) != k1_zfmisc_1(k2_struct_0(sK3)) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_5561]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1,plain,
% 3.55/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.55/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1131,plain,
% 3.55/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_0,plain,
% 3.55/1.01      ( k2_subset_1(X0) = X0 ),
% 3.55/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1132,plain,
% 3.55/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.55/1.01      inference(light_normalisation,[status(thm)],[c_1131,c_0]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_5,plain,
% 3.55/1.01      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.55/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1127,plain,
% 3.55/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_17,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 3.55/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/1.01      | v2_struct_0(X1)
% 3.55/1.01      | ~ v3_orders_2(X1)
% 3.55/1.01      | ~ v4_orders_2(X1)
% 3.55/1.01      | ~ v5_orders_2(X1)
% 3.55/1.01      | ~ l1_orders_2(X1)
% 3.55/1.01      | sK2(X0,X1,X2) = X0 ),
% 3.55/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_21,negated_conjecture,
% 3.55/1.01      ( v5_orders_2(sK3) ),
% 3.55/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_473,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 3.55/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/1.01      | v2_struct_0(X1)
% 3.55/1.01      | ~ v3_orders_2(X1)
% 3.55/1.01      | ~ v4_orders_2(X1)
% 3.55/1.01      | ~ l1_orders_2(X1)
% 3.55/1.01      | sK2(X0,X1,X2) = X0
% 3.55/1.01      | sK3 != X1 ),
% 3.55/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_474,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
% 3.55/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.55/1.01      | v2_struct_0(sK3)
% 3.55/1.01      | ~ v3_orders_2(sK3)
% 3.55/1.01      | ~ v4_orders_2(sK3)
% 3.55/1.01      | ~ l1_orders_2(sK3)
% 3.55/1.01      | sK2(X0,sK3,X1) = X0 ),
% 3.55/1.01      inference(unflattening,[status(thm)],[c_473]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_24,negated_conjecture,
% 3.55/1.01      ( ~ v2_struct_0(sK3) ),
% 3.55/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_23,negated_conjecture,
% 3.55/1.01      ( v3_orders_2(sK3) ),
% 3.55/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_22,negated_conjecture,
% 3.55/1.01      ( v4_orders_2(sK3) ),
% 3.55/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_20,negated_conjecture,
% 3.55/1.01      ( l1_orders_2(sK3) ),
% 3.55/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_478,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
% 3.55/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.55/1.01      | sK2(X0,sK3,X1) = X0 ),
% 3.55/1.01      inference(global_propositional_subsumption,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_474,c_24,c_23,c_22,c_20]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1123,plain,
% 3.55/1.01      ( sK2(X0,sK3,X1) = X0
% 3.55/1.01      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.55/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_12,plain,
% 3.55/1.01      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.55/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_6,plain,
% 3.55/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.55/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_263,plain,
% 3.55/1.01      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.55/1.01      inference(resolution,[status(thm)],[c_12,c_6]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_612,plain,
% 3.55/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 3.55/1.01      inference(resolution_lifted,[status(thm)],[c_263,c_20]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_613,plain,
% 3.55/1.01      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.55/1.01      inference(unflattening,[status(thm)],[c_612]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1136,plain,
% 3.55/1.01      ( sK2(X0,sK3,X1) = X0
% 3.55/1.01      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.55/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.55/1.01      inference(light_normalisation,[status(thm)],[c_1123,c_613]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1493,plain,
% 3.55/1.01      ( sK2(sK0(a_2_1_orders_2(sK3,X0)),sK3,X0) = sK0(a_2_1_orders_2(sK3,X0))
% 3.55/1.01      | a_2_1_orders_2(sK3,X0) = k1_xboole_0
% 3.55/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_1127,c_1136]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2526,plain,
% 3.55/1.01      ( sK2(sK0(a_2_1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(a_2_1_orders_2(sK3,k2_struct_0(sK3)))
% 3.55/1.01      | a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_1132,c_1493]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_10,plain,
% 3.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/1.01      | v2_struct_0(X1)
% 3.55/1.01      | ~ v3_orders_2(X1)
% 3.55/1.01      | ~ v4_orders_2(X1)
% 3.55/1.01      | ~ v5_orders_2(X1)
% 3.55/1.01      | ~ l1_orders_2(X1)
% 3.55/1.01      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 3.55/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_560,plain,
% 3.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/1.01      | v2_struct_0(X1)
% 3.55/1.01      | ~ v3_orders_2(X1)
% 3.55/1.01      | ~ v4_orders_2(X1)
% 3.55/1.01      | ~ l1_orders_2(X1)
% 3.55/1.01      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0)
% 3.55/1.01      | sK3 != X1 ),
% 3.55/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_561,plain,
% 3.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.55/1.01      | v2_struct_0(sK3)
% 3.55/1.01      | ~ v3_orders_2(sK3)
% 3.55/1.01      | ~ v4_orders_2(sK3)
% 3.55/1.01      | ~ l1_orders_2(sK3)
% 3.55/1.01      | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
% 3.55/1.01      inference(unflattening,[status(thm)],[c_560]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_565,plain,
% 3.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.55/1.01      | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
% 3.55/1.01      inference(global_propositional_subsumption,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_561,c_24,c_23,c_22,c_20]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1119,plain,
% 3.55/1.01      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 3.55/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1134,plain,
% 3.55/1.01      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 3.55/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.55/1.01      inference(light_normalisation,[status(thm)],[c_1119,c_613]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1559,plain,
% 3.55/1.01      ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_1132,c_1134]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2528,plain,
% 3.55/1.01      ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
% 3.55/1.01      | a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 3.55/1.01      inference(light_normalisation,[status(thm)],[c_2526,c_1559]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2529,plain,
% 3.55/1.01      ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
% 3.55/1.01      | k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 3.55/1.01      inference(demodulation,[status(thm)],[c_2528,c_1559]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_19,negated_conjecture,
% 3.55/1.01      ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.55/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_859,plain,( X0 = X0 ),theory(equality) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_6965,plain,
% 3.55/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_859]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_860,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1305,plain,
% 3.55/1.01      ( k2_orders_2(X0,X1) != X2
% 3.55/1.01      | k1_xboole_0 != X2
% 3.55/1.01      | k1_xboole_0 = k2_orders_2(X0,X1) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_860]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_4593,plain,
% 3.55/1.01      ( k2_orders_2(X0,k2_struct_0(sK3)) != X1
% 3.55/1.01      | k1_xboole_0 != X1
% 3.55/1.01      | k1_xboole_0 = k2_orders_2(X0,k2_struct_0(sK3)) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_1305]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_9335,plain,
% 3.55/1.01      ( k2_orders_2(X0,k2_struct_0(sK3)) != k1_xboole_0
% 3.55/1.01      | k1_xboole_0 = k2_orders_2(X0,k2_struct_0(sK3))
% 3.55/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_4593]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_9336,plain,
% 3.55/1.01      ( k2_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
% 3.55/1.01      | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3))
% 3.55/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_9335]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_10794,plain,
% 3.55/1.01      ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3))) ),
% 3.55/1.01      inference(global_propositional_subsumption,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_2529,c_19,c_6965,c_9336]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_16,plain,
% 3.55/1.01      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 3.55/1.01      | ~ r2_hidden(X3,X2)
% 3.55/1.01      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 3.55/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.55/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.55/1.01      | v2_struct_0(X0)
% 3.55/1.01      | ~ v3_orders_2(X0)
% 3.55/1.01      | ~ v4_orders_2(X0)
% 3.55/1.01      | ~ v5_orders_2(X0)
% 3.55/1.01      | ~ l1_orders_2(X0) ),
% 3.55/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_399,plain,
% 3.55/1.01      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 3.55/1.01      | ~ r2_hidden(X3,X2)
% 3.55/1.01      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 3.55/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.55/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.55/1.01      | v2_struct_0(X0)
% 3.55/1.01      | ~ v3_orders_2(X0)
% 3.55/1.01      | ~ v4_orders_2(X0)
% 3.55/1.01      | ~ l1_orders_2(X0)
% 3.55/1.01      | sK3 != X0 ),
% 3.55/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_400,plain,
% 3.55/1.01      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
% 3.55/1.01      | ~ r2_hidden(X2,X1)
% 3.55/1.01      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
% 3.55/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 3.55/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.55/1.01      | v2_struct_0(sK3)
% 3.55/1.01      | ~ v3_orders_2(sK3)
% 3.55/1.01      | ~ v4_orders_2(sK3)
% 3.55/1.01      | ~ l1_orders_2(sK3) ),
% 3.55/1.01      inference(unflattening,[status(thm)],[c_399]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_404,plain,
% 3.55/1.01      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
% 3.55/1.01      | ~ r2_hidden(X2,X1)
% 3.55/1.01      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
% 3.55/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 3.55/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.55/1.01      inference(global_propositional_subsumption,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_400,c_24,c_23,c_22,c_20]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,X1)
% 3.55/1.01      | m1_subset_1(X0,X2)
% 3.55/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.55/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_420,plain,
% 3.55/1.01      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
% 3.55/1.01      | ~ r2_hidden(X2,X1)
% 3.55/1.01      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
% 3.55/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.55/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_404,c_3]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1126,plain,
% 3.55/1.01      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
% 3.55/1.01      | r2_hidden(X2,X1) != iProver_top
% 3.55/1.01      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.55/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1140,plain,
% 3.55/1.01      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
% 3.55/1.01      | r2_hidden(X2,X1) != iProver_top
% 3.55/1.01      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.55/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.55/1.01      inference(light_normalisation,[status(thm)],[c_1126,c_613]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_8,plain,
% 3.55/1.01      ( ~ r2_orders_2(X0,X1,X1)
% 3.55/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.55/1.01      | ~ l1_orders_2(X0) ),
% 3.55/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_617,plain,
% 3.55/1.01      ( ~ r2_orders_2(X0,X1,X1)
% 3.55/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.55/1.01      | sK3 != X0 ),
% 3.55/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_618,plain,
% 3.55/1.01      ( ~ r2_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.55/1.01      inference(unflattening,[status(thm)],[c_617]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1118,plain,
% 3.55/1.01      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 3.55/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1133,plain,
% 3.55/1.01      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 3.55/1.01      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 3.55/1.01      inference(light_normalisation,[status(thm)],[c_1118,c_613]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1458,plain,
% 3.55/1.01      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.55/1.01      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 3.55/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.55/1.01      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) != iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_1140,c_1133]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_18,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 3.55/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/1.01      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 3.55/1.01      | v2_struct_0(X1)
% 3.55/1.01      | ~ v3_orders_2(X1)
% 3.55/1.01      | ~ v4_orders_2(X1)
% 3.55/1.01      | ~ v5_orders_2(X1)
% 3.55/1.01      | ~ l1_orders_2(X1) ),
% 3.55/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_452,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 3.55/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/1.01      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 3.55/1.01      | v2_struct_0(X1)
% 3.55/1.01      | ~ v3_orders_2(X1)
% 3.55/1.01      | ~ v4_orders_2(X1)
% 3.55/1.01      | ~ l1_orders_2(X1)
% 3.55/1.01      | sK3 != X1 ),
% 3.55/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_453,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
% 3.55/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.55/1.01      | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3))
% 3.55/1.01      | v2_struct_0(sK3)
% 3.55/1.01      | ~ v3_orders_2(sK3)
% 3.55/1.01      | ~ v4_orders_2(sK3)
% 3.55/1.01      | ~ l1_orders_2(sK3) ),
% 3.55/1.01      inference(unflattening,[status(thm)],[c_452]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_457,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
% 3.55/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.55/1.01      | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) ),
% 3.55/1.01      inference(global_propositional_subsumption,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_453,c_24,c_23,c_22,c_20]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1124,plain,
% 3.55/1.01      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.55/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.55/1.01      | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) = iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1137,plain,
% 3.55/1.01      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.55/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.55/1.01      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top ),
% 3.55/1.01      inference(light_normalisation,[status(thm)],[c_1124,c_613]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2049,plain,
% 3.55/1.01      ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.55/1.01      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 3.55/1.01      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 3.55/1.01      inference(global_propositional_subsumption,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_1458,c_1137]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2050,plain,
% 3.55/1.01      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.55/1.01      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 3.55/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.55/1.01      inference(renaming,[status(thm)],[c_2049]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_10799,plain,
% 3.55/1.01      ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.55/1.01      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top
% 3.55/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_10794,c_2050]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_10804,plain,
% 3.55/1.01      ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.55/1.01      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top
% 3.55/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.55/1.01      inference(light_normalisation,[status(thm)],[c_10799,c_1559]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_10810,plain,
% 3.55/1.01      ( ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
% 3.55/1.01      | ~ r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3))
% 3.55/1.01      | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) ),
% 3.55/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_10804]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_8552,plain,
% 3.55/1.01      ( k1_zfmisc_1(k2_struct_0(sK3)) = k1_zfmisc_1(k2_struct_0(sK3)) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_859]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_11,plain,
% 3.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/1.01      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/1.01      | v2_struct_0(X1)
% 3.55/1.01      | ~ v3_orders_2(X1)
% 3.55/1.01      | ~ v4_orders_2(X1)
% 3.55/1.01      | ~ v5_orders_2(X1)
% 3.55/1.01      | ~ l1_orders_2(X1) ),
% 3.55/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_542,plain,
% 3.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/1.01      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/1.01      | v2_struct_0(X1)
% 3.55/1.01      | ~ v3_orders_2(X1)
% 3.55/1.01      | ~ v4_orders_2(X1)
% 3.55/1.01      | ~ l1_orders_2(X1)
% 3.55/1.01      | sK3 != X1 ),
% 3.55/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_543,plain,
% 3.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.55/1.01      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.55/1.01      | v2_struct_0(sK3)
% 3.55/1.01      | ~ v3_orders_2(sK3)
% 3.55/1.01      | ~ v4_orders_2(sK3)
% 3.55/1.01      | ~ l1_orders_2(sK3) ),
% 3.55/1.01      inference(unflattening,[status(thm)],[c_542]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_547,plain,
% 3.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.55/1.01      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.55/1.01      inference(global_propositional_subsumption,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_543,c_24,c_23,c_22,c_20]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1120,plain,
% 3.55/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.55/1.01      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1135,plain,
% 3.55/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.55/1.01      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 3.55/1.01      inference(light_normalisation,[status(thm)],[c_1120,c_613]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1129,plain,
% 3.55/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.55/1.01      | m1_subset_1(X0,X2) = iProver_top
% 3.55/1.01      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2113,plain,
% 3.55/1.01      ( r2_hidden(X0,k2_orders_2(sK3,X1)) != iProver_top
% 3.55/1.01      | m1_subset_1(X0,k2_struct_0(sK3)) = iProver_top
% 3.55/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_1135,c_1129]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2351,plain,
% 3.55/1.01      ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.55/1.01      | m1_subset_1(X0,k2_struct_0(sK3)) = iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_1132,c_2113]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3345,plain,
% 3.55/1.01      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 3.55/1.01      | m1_subset_1(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_1127,c_2351]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2,plain,
% 3.55/1.01      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 3.55/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1130,plain,
% 3.55/1.01      ( r2_hidden(X0,X1) = iProver_top
% 3.55/1.01      | m1_subset_1(X0,X1) != iProver_top
% 3.55/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_3618,plain,
% 3.55/1.01      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 3.55/1.01      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
% 3.55/1.01      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_3345,c_1130]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_4,plain,
% 3.55/1.01      ( ~ r2_hidden(X0,X1)
% 3.55/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.55/1.01      | ~ v1_xboole_0(X2) ),
% 3.55/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1128,plain,
% 3.55/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.55/1.01      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.55/1.01      | v1_xboole_0(X2) != iProver_top ),
% 3.55/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1722,plain,
% 3.55/1.01      ( r2_hidden(X0,k2_orders_2(sK3,X1)) != iProver_top
% 3.55/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.55/1.01      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_1135,c_1128]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1951,plain,
% 3.55/1.01      ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.55/1.01      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_1132,c_1722]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2785,plain,
% 3.55/1.01      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 3.55/1.01      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.55/1.01      inference(superposition,[status(thm)],[c_1127,c_1951]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_6083,plain,
% 3.55/1.01      ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
% 3.55/1.01      | k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 3.55/1.01      inference(global_propositional_subsumption,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_3618,c_2785]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_6084,plain,
% 3.55/1.01      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 3.55/1.01      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
% 3.55/1.01      inference(renaming,[status(thm)],[c_6083]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_6085,plain,
% 3.55/1.01      ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3))
% 3.55/1.01      | k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 3.55/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_6084]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_5208,plain,
% 3.55/1.01      ( m1_subset_1(k2_subset_1(k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3))) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1936,plain,
% 3.55/1.01      ( X0 != X1 | k2_struct_0(sK3) != X1 | k2_struct_0(sK3) = X0 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_860]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_2864,plain,
% 3.55/1.01      ( X0 != k2_struct_0(sK3)
% 3.55/1.01      | k2_struct_0(sK3) = X0
% 3.55/1.01      | k2_struct_0(sK3) != k2_struct_0(sK3) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_1936]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_4240,plain,
% 3.55/1.01      ( k2_struct_0(sK3) != k2_struct_0(sK3)
% 3.55/1.01      | k2_struct_0(sK3) = k2_subset_1(k2_struct_0(sK3))
% 3.55/1.01      | k2_subset_1(k2_struct_0(sK3)) != k2_struct_0(sK3) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_2864]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1856,plain,
% 3.55/1.01      ( k2_subset_1(k2_struct_0(sK3)) = k2_struct_0(sK3) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_1185,plain,
% 3.55/1.01      ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
% 3.55/1.01      | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_882,plain,
% 3.55/1.01      ( sK3 = sK3 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_859]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_864,plain,
% 3.55/1.01      ( X0 != X1 | k2_struct_0(X0) = k2_struct_0(X1) ),
% 3.55/1.01      theory(equality) ).
% 3.55/1.01  
% 3.55/1.01  cnf(c_874,plain,
% 3.55/1.01      ( k2_struct_0(sK3) = k2_struct_0(sK3) | sK3 != sK3 ),
% 3.55/1.01      inference(instantiation,[status(thm)],[c_864]) ).
% 3.55/1.01  
% 3.55/1.01  cnf(contradiction,plain,
% 3.55/1.01      ( $false ),
% 3.55/1.01      inference(minisat,
% 3.55/1.01                [status(thm)],
% 3.55/1.01                [c_11043,c_10810,c_9336,c_8552,c_6965,c_6085,c_5208,
% 3.55/1.01                 c_4240,c_1856,c_1185,c_882,c_874,c_19]) ).
% 3.55/1.01  
% 3.55/1.01  
% 3.55/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.55/1.01  
% 3.55/1.01  ------                               Statistics
% 3.55/1.01  
% 3.55/1.01  ------ General
% 3.55/1.01  
% 3.55/1.01  abstr_ref_over_cycles:                  0
% 3.55/1.01  abstr_ref_under_cycles:                 0
% 3.55/1.01  gc_basic_clause_elim:                   0
% 3.55/1.01  forced_gc_time:                         0
% 3.55/1.01  parsing_time:                           0.01
% 3.55/1.01  unif_index_cands_time:                  0.
% 3.55/1.01  unif_index_add_time:                    0.
% 3.55/1.01  orderings_time:                         0.
% 3.55/1.01  out_proof_time:                         0.013
% 3.55/1.01  total_time:                             0.484
% 3.55/1.01  num_of_symbols:                         53
% 3.55/1.01  num_of_terms:                           12374
% 3.55/1.01  
% 3.55/1.01  ------ Preprocessing
% 3.55/1.01  
% 3.55/1.01  num_of_splits:                          0
% 3.55/1.01  num_of_split_atoms:                     0
% 3.55/1.01  num_of_reused_defs:                     0
% 3.55/1.01  num_eq_ax_congr_red:                    33
% 3.55/1.01  num_of_sem_filtered_clauses:            1
% 3.55/1.01  num_of_subtypes:                        0
% 3.55/1.01  monotx_restored_types:                  0
% 3.55/1.01  sat_num_of_epr_types:                   0
% 3.55/1.01  sat_num_of_non_cyclic_types:            0
% 3.55/1.01  sat_guarded_non_collapsed_types:        0
% 3.55/1.01  num_pure_diseq_elim:                    0
% 3.55/1.01  simp_replaced_by:                       0
% 3.55/1.01  res_preprocessed:                       101
% 3.55/1.01  prep_upred:                             0
% 3.55/1.01  prep_unflattend:                        26
% 3.55/1.01  smt_new_axioms:                         0
% 3.55/1.01  pred_elim_cands:                        4
% 3.55/1.01  pred_elim:                              7
% 3.55/1.01  pred_elim_cl:                           8
% 3.55/1.01  pred_elim_cycles:                       12
% 3.55/1.01  merged_defs:                            0
% 3.55/1.01  merged_defs_ncl:                        0
% 3.55/1.01  bin_hyper_res:                          0
% 3.55/1.01  prep_cycles:                            4
% 3.55/1.01  pred_elim_time:                         0.021
% 3.55/1.01  splitting_time:                         0.
% 3.55/1.01  sem_filter_time:                        0.
% 3.55/1.01  monotx_time:                            0.001
% 3.55/1.01  subtype_inf_time:                       0.
% 3.55/1.01  
% 3.55/1.01  ------ Problem properties
% 3.55/1.01  
% 3.55/1.01  clauses:                                17
% 3.55/1.01  conjectures:                            1
% 3.55/1.01  epr:                                    1
% 3.55/1.01  horn:                                   13
% 3.55/1.01  ground:                                 2
% 3.55/1.01  unary:                                  4
% 3.55/1.01  binary:                                 4
% 3.55/1.01  lits:                                   43
% 3.55/1.01  lits_eq:                                6
% 3.55/1.01  fd_pure:                                0
% 3.55/1.01  fd_pseudo:                              0
% 3.55/1.01  fd_cond:                                1
% 3.55/1.01  fd_pseudo_cond:                         0
% 3.55/1.01  ac_symbols:                             0
% 3.55/1.01  
% 3.55/1.01  ------ Propositional Solver
% 3.55/1.01  
% 3.55/1.01  prop_solver_calls:                      31
% 3.55/1.01  prop_fast_solver_calls:                 1345
% 3.55/1.01  smt_solver_calls:                       0
% 3.55/1.01  smt_fast_solver_calls:                  0
% 3.55/1.01  prop_num_of_clauses:                    6151
% 3.55/1.01  prop_preprocess_simplified:             10078
% 3.55/1.01  prop_fo_subsumed:                       60
% 3.55/1.01  prop_solver_time:                       0.
% 3.55/1.01  smt_solver_time:                        0.
% 3.55/1.01  smt_fast_solver_time:                   0.
% 3.55/1.01  prop_fast_solver_time:                  0.
% 3.55/1.01  prop_unsat_core_time:                   0.
% 3.55/1.01  
% 3.55/1.01  ------ QBF
% 3.55/1.01  
% 3.55/1.01  qbf_q_res:                              0
% 3.55/1.01  qbf_num_tautologies:                    0
% 3.55/1.01  qbf_prep_cycles:                        0
% 3.55/1.01  
% 3.55/1.01  ------ BMC1
% 3.55/1.01  
% 3.55/1.01  bmc1_current_bound:                     -1
% 3.55/1.01  bmc1_last_solved_bound:                 -1
% 3.55/1.01  bmc1_unsat_core_size:                   -1
% 3.55/1.01  bmc1_unsat_core_parents_size:           -1
% 3.55/1.01  bmc1_merge_next_fun:                    0
% 3.55/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.55/1.01  
% 3.55/1.01  ------ Instantiation
% 3.55/1.01  
% 3.55/1.01  inst_num_of_clauses:                    1577
% 3.55/1.01  inst_num_in_passive:                    90
% 3.55/1.01  inst_num_in_active:                     844
% 3.55/1.01  inst_num_in_unprocessed:                643
% 3.55/1.01  inst_num_of_loops:                      938
% 3.55/1.01  inst_num_of_learning_restarts:          0
% 3.55/1.01  inst_num_moves_active_passive:          88
% 3.55/1.01  inst_lit_activity:                      0
% 3.55/1.01  inst_lit_activity_moves:                0
% 3.55/1.01  inst_num_tautologies:                   0
% 3.55/1.01  inst_num_prop_implied:                  0
% 3.55/1.01  inst_num_existing_simplified:           0
% 3.55/1.01  inst_num_eq_res_simplified:             0
% 3.55/1.01  inst_num_child_elim:                    0
% 3.55/1.01  inst_num_of_dismatching_blockings:      448
% 3.55/1.01  inst_num_of_non_proper_insts:           1590
% 3.55/1.01  inst_num_of_duplicates:                 0
% 3.55/1.01  inst_inst_num_from_inst_to_res:         0
% 3.55/1.01  inst_dismatching_checking_time:         0.
% 3.55/1.01  
% 3.55/1.01  ------ Resolution
% 3.55/1.01  
% 3.55/1.01  res_num_of_clauses:                     0
% 3.55/1.01  res_num_in_passive:                     0
% 3.55/1.01  res_num_in_active:                      0
% 3.55/1.01  res_num_of_loops:                       105
% 3.55/1.01  res_forward_subset_subsumed:            210
% 3.55/1.01  res_backward_subset_subsumed:           2
% 3.55/1.01  res_forward_subsumed:                   0
% 3.55/1.01  res_backward_subsumed:                  0
% 3.55/1.01  res_forward_subsumption_resolution:     2
% 3.55/1.01  res_backward_subsumption_resolution:    0
% 3.55/1.01  res_clause_to_clause_subsumption:       4437
% 3.55/1.01  res_orphan_elimination:                 0
% 3.55/1.01  res_tautology_del:                      132
% 3.55/1.01  res_num_eq_res_simplified:              0
% 3.55/1.01  res_num_sel_changes:                    0
% 3.55/1.01  res_moves_from_active_to_pass:          0
% 3.55/1.01  
% 3.55/1.01  ------ Superposition
% 3.55/1.01  
% 3.55/1.01  sup_time_total:                         0.
% 3.55/1.01  sup_time_generating:                    0.
% 3.55/1.01  sup_time_sim_full:                      0.
% 3.55/1.01  sup_time_sim_immed:                     0.
% 3.55/1.01  
% 3.55/1.01  sup_num_of_clauses:                     592
% 3.55/1.01  sup_num_in_active:                      116
% 3.55/1.01  sup_num_in_passive:                     476
% 3.55/1.01  sup_num_of_loops:                       186
% 3.55/1.01  sup_fw_superposition:                   497
% 3.55/1.01  sup_bw_superposition:                   223
% 3.55/1.01  sup_immediate_simplified:               114
% 3.55/1.01  sup_given_eliminated:                   1
% 3.55/1.01  comparisons_done:                       0
% 3.55/1.01  comparisons_avoided:                    9
% 3.55/1.01  
% 3.55/1.01  ------ Simplifications
% 3.55/1.01  
% 3.55/1.01  
% 3.55/1.01  sim_fw_subset_subsumed:                 3
% 3.55/1.01  sim_bw_subset_subsumed:                 2
% 3.55/1.01  sim_fw_subsumed:                        16
% 3.55/1.01  sim_bw_subsumed:                        70
% 3.55/1.01  sim_fw_subsumption_res:                 0
% 3.55/1.01  sim_bw_subsumption_res:                 0
% 3.55/1.01  sim_tautology_del:                      3
% 3.55/1.01  sim_eq_tautology_del:                   0
% 3.55/1.01  sim_eq_res_simp:                        0
% 3.55/1.01  sim_fw_demodulated:                     23
% 3.55/1.01  sim_bw_demodulated:                     0
% 3.55/1.01  sim_light_normalised:                   93
% 3.55/1.01  sim_joinable_taut:                      0
% 3.55/1.01  sim_joinable_simp:                      0
% 3.55/1.01  sim_ac_normalised:                      0
% 3.55/1.01  sim_smt_subsumption:                    0
% 3.55/1.01  
%------------------------------------------------------------------------------
