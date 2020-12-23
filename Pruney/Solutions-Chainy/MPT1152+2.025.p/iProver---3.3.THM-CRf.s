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
% DateTime   : Thu Dec  3 12:12:14 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 556 expanded)
%              Number of clauses        :   64 ( 158 expanded)
%              Number of leaves         :   15 ( 118 expanded)
%              Depth                    :   20
%              Number of atoms          :  538 (2674 expanded)
%              Number of equality atoms :  123 ( 488 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f29])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f36,plain,(
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

fof(f35,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f27,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,
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

fof(f39,plain,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f38])).

fof(f62,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f37])).

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

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1177,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_24,c_23,c_22,c_20])).

cnf(c_1174,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_12,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_301,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_12,c_5])).

cnf(c_619,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_301,c_20])).

cnf(c_620,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_1239,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1174,c_620])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1181,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1592,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1239,c_1181])).

cnf(c_16,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_407,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_408,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_412,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_24,c_23,c_22,c_20])).

cnf(c_1176,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_412])).

cnf(c_1273,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
    | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1176,c_620])).

cnf(c_8,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_631,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_632,plain,
    ( ~ r2_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_1167,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_1193,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1167,c_620])).

cnf(c_2008,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1273,c_1193])).

cnf(c_4693,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2008,c_1239])).

cnf(c_4702,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_4693])).

cnf(c_6,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_290,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_12,c_6])).

cnf(c_624,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_290,c_20])).

cnf(c_625,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_1168,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_1186,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1168,c_620])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_571,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_567,c_24,c_23,c_22,c_20])).

cnf(c_1169,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_1198,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1169,c_620])).

cnf(c_1382,plain,
    ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1186,c_1198])).

cnf(c_4703,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4702,c_1382])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_548,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_549,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_549,c_24,c_23,c_22,c_20])).

cnf(c_1170,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(c_1209,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1170,c_620])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1180,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1919,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,k2_orders_2(sK3,X0)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_1180])).

cnf(c_2481,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1186,c_1919])).

cnf(c_5086,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4703,c_1186,c_2481])).

cnf(c_5093,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1177,c_5086])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5129,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5093,c_19])).

cnf(c_5130,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_5129])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.76/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.00  
% 2.76/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.76/1.00  
% 2.76/1.00  ------  iProver source info
% 2.76/1.00  
% 2.76/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.76/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.76/1.00  git: non_committed_changes: false
% 2.76/1.00  git: last_make_outside_of_git: false
% 2.76/1.00  
% 2.76/1.00  ------ 
% 2.76/1.00  
% 2.76/1.00  ------ Input Options
% 2.76/1.00  
% 2.76/1.00  --out_options                           all
% 2.76/1.00  --tptp_safe_out                         true
% 2.76/1.00  --problem_path                          ""
% 2.76/1.00  --include_path                          ""
% 2.76/1.00  --clausifier                            res/vclausify_rel
% 2.76/1.00  --clausifier_options                    --mode clausify
% 2.76/1.00  --stdin                                 false
% 2.76/1.00  --stats_out                             all
% 2.76/1.00  
% 2.76/1.00  ------ General Options
% 2.76/1.00  
% 2.76/1.00  --fof                                   false
% 2.76/1.00  --time_out_real                         305.
% 2.76/1.00  --time_out_virtual                      -1.
% 2.76/1.00  --symbol_type_check                     false
% 2.76/1.00  --clausify_out                          false
% 2.76/1.00  --sig_cnt_out                           false
% 2.76/1.00  --trig_cnt_out                          false
% 2.76/1.00  --trig_cnt_out_tolerance                1.
% 2.76/1.00  --trig_cnt_out_sk_spl                   false
% 2.76/1.00  --abstr_cl_out                          false
% 2.76/1.00  
% 2.76/1.00  ------ Global Options
% 2.76/1.00  
% 2.76/1.00  --schedule                              default
% 2.76/1.00  --add_important_lit                     false
% 2.76/1.00  --prop_solver_per_cl                    1000
% 2.76/1.00  --min_unsat_core                        false
% 2.76/1.00  --soft_assumptions                      false
% 2.76/1.00  --soft_lemma_size                       3
% 2.76/1.00  --prop_impl_unit_size                   0
% 2.76/1.00  --prop_impl_unit                        []
% 2.76/1.00  --share_sel_clauses                     true
% 2.76/1.00  --reset_solvers                         false
% 2.76/1.00  --bc_imp_inh                            [conj_cone]
% 2.76/1.00  --conj_cone_tolerance                   3.
% 2.76/1.00  --extra_neg_conj                        none
% 2.76/1.00  --large_theory_mode                     true
% 2.76/1.00  --prolific_symb_bound                   200
% 2.76/1.00  --lt_threshold                          2000
% 2.76/1.00  --clause_weak_htbl                      true
% 2.76/1.00  --gc_record_bc_elim                     false
% 2.76/1.00  
% 2.76/1.00  ------ Preprocessing Options
% 2.76/1.00  
% 2.76/1.00  --preprocessing_flag                    true
% 2.76/1.00  --time_out_prep_mult                    0.1
% 2.76/1.00  --splitting_mode                        input
% 2.76/1.00  --splitting_grd                         true
% 2.76/1.00  --splitting_cvd                         false
% 2.76/1.00  --splitting_cvd_svl                     false
% 2.76/1.00  --splitting_nvd                         32
% 2.76/1.00  --sub_typing                            true
% 2.76/1.00  --prep_gs_sim                           true
% 2.76/1.00  --prep_unflatten                        true
% 2.76/1.00  --prep_res_sim                          true
% 2.76/1.00  --prep_upred                            true
% 2.76/1.00  --prep_sem_filter                       exhaustive
% 2.76/1.00  --prep_sem_filter_out                   false
% 2.76/1.00  --pred_elim                             true
% 2.76/1.00  --res_sim_input                         true
% 2.76/1.00  --eq_ax_congr_red                       true
% 2.76/1.00  --pure_diseq_elim                       true
% 2.76/1.00  --brand_transform                       false
% 2.76/1.00  --non_eq_to_eq                          false
% 2.76/1.00  --prep_def_merge                        true
% 2.76/1.00  --prep_def_merge_prop_impl              false
% 2.76/1.00  --prep_def_merge_mbd                    true
% 2.76/1.00  --prep_def_merge_tr_red                 false
% 2.76/1.00  --prep_def_merge_tr_cl                  false
% 2.76/1.00  --smt_preprocessing                     true
% 2.76/1.00  --smt_ac_axioms                         fast
% 2.76/1.00  --preprocessed_out                      false
% 2.76/1.00  --preprocessed_stats                    false
% 2.76/1.00  
% 2.76/1.00  ------ Abstraction refinement Options
% 2.76/1.00  
% 2.76/1.00  --abstr_ref                             []
% 2.76/1.00  --abstr_ref_prep                        false
% 2.76/1.00  --abstr_ref_until_sat                   false
% 2.76/1.00  --abstr_ref_sig_restrict                funpre
% 2.76/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/1.00  --abstr_ref_under                       []
% 2.76/1.00  
% 2.76/1.00  ------ SAT Options
% 2.76/1.00  
% 2.76/1.00  --sat_mode                              false
% 2.76/1.00  --sat_fm_restart_options                ""
% 2.76/1.00  --sat_gr_def                            false
% 2.76/1.00  --sat_epr_types                         true
% 2.76/1.00  --sat_non_cyclic_types                  false
% 2.76/1.00  --sat_finite_models                     false
% 2.76/1.00  --sat_fm_lemmas                         false
% 2.76/1.00  --sat_fm_prep                           false
% 2.76/1.00  --sat_fm_uc_incr                        true
% 2.76/1.00  --sat_out_model                         small
% 2.76/1.00  --sat_out_clauses                       false
% 2.76/1.00  
% 2.76/1.00  ------ QBF Options
% 2.76/1.00  
% 2.76/1.00  --qbf_mode                              false
% 2.76/1.00  --qbf_elim_univ                         false
% 2.76/1.00  --qbf_dom_inst                          none
% 2.76/1.00  --qbf_dom_pre_inst                      false
% 2.76/1.00  --qbf_sk_in                             false
% 2.76/1.00  --qbf_pred_elim                         true
% 2.76/1.00  --qbf_split                             512
% 2.76/1.00  
% 2.76/1.00  ------ BMC1 Options
% 2.76/1.00  
% 2.76/1.00  --bmc1_incremental                      false
% 2.76/1.00  --bmc1_axioms                           reachable_all
% 2.76/1.00  --bmc1_min_bound                        0
% 2.76/1.00  --bmc1_max_bound                        -1
% 2.76/1.00  --bmc1_max_bound_default                -1
% 2.76/1.00  --bmc1_symbol_reachability              true
% 2.76/1.00  --bmc1_property_lemmas                  false
% 2.76/1.00  --bmc1_k_induction                      false
% 2.76/1.00  --bmc1_non_equiv_states                 false
% 2.76/1.00  --bmc1_deadlock                         false
% 2.76/1.00  --bmc1_ucm                              false
% 2.76/1.00  --bmc1_add_unsat_core                   none
% 2.76/1.00  --bmc1_unsat_core_children              false
% 2.76/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/1.00  --bmc1_out_stat                         full
% 2.76/1.00  --bmc1_ground_init                      false
% 2.76/1.00  --bmc1_pre_inst_next_state              false
% 2.76/1.00  --bmc1_pre_inst_state                   false
% 2.76/1.00  --bmc1_pre_inst_reach_state             false
% 2.76/1.00  --bmc1_out_unsat_core                   false
% 2.76/1.00  --bmc1_aig_witness_out                  false
% 2.76/1.00  --bmc1_verbose                          false
% 2.76/1.00  --bmc1_dump_clauses_tptp                false
% 2.76/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.76/1.00  --bmc1_dump_file                        -
% 2.76/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.76/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.76/1.00  --bmc1_ucm_extend_mode                  1
% 2.76/1.00  --bmc1_ucm_init_mode                    2
% 2.76/1.00  --bmc1_ucm_cone_mode                    none
% 2.76/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.76/1.00  --bmc1_ucm_relax_model                  4
% 2.76/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.76/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/1.00  --bmc1_ucm_layered_model                none
% 2.76/1.00  --bmc1_ucm_max_lemma_size               10
% 2.76/1.00  
% 2.76/1.00  ------ AIG Options
% 2.76/1.00  
% 2.76/1.00  --aig_mode                              false
% 2.76/1.00  
% 2.76/1.00  ------ Instantiation Options
% 2.76/1.00  
% 2.76/1.00  --instantiation_flag                    true
% 2.76/1.00  --inst_sos_flag                         false
% 2.76/1.00  --inst_sos_phase                        true
% 2.76/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/1.00  --inst_lit_sel_side                     num_symb
% 2.76/1.00  --inst_solver_per_active                1400
% 2.76/1.00  --inst_solver_calls_frac                1.
% 2.76/1.00  --inst_passive_queue_type               priority_queues
% 2.76/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/1.00  --inst_passive_queues_freq              [25;2]
% 2.76/1.00  --inst_dismatching                      true
% 2.76/1.00  --inst_eager_unprocessed_to_passive     true
% 2.76/1.00  --inst_prop_sim_given                   true
% 2.76/1.00  --inst_prop_sim_new                     false
% 2.76/1.00  --inst_subs_new                         false
% 2.76/1.00  --inst_eq_res_simp                      false
% 2.76/1.00  --inst_subs_given                       false
% 2.76/1.00  --inst_orphan_elimination               true
% 2.76/1.00  --inst_learning_loop_flag               true
% 2.76/1.00  --inst_learning_start                   3000
% 2.76/1.00  --inst_learning_factor                  2
% 2.76/1.00  --inst_start_prop_sim_after_learn       3
% 2.76/1.00  --inst_sel_renew                        solver
% 2.76/1.00  --inst_lit_activity_flag                true
% 2.76/1.00  --inst_restr_to_given                   false
% 2.76/1.00  --inst_activity_threshold               500
% 2.76/1.00  --inst_out_proof                        true
% 2.76/1.00  
% 2.76/1.00  ------ Resolution Options
% 2.76/1.00  
% 2.76/1.00  --resolution_flag                       true
% 2.76/1.00  --res_lit_sel                           adaptive
% 2.76/1.00  --res_lit_sel_side                      none
% 2.76/1.00  --res_ordering                          kbo
% 2.76/1.00  --res_to_prop_solver                    active
% 2.76/1.00  --res_prop_simpl_new                    false
% 2.76/1.00  --res_prop_simpl_given                  true
% 2.76/1.00  --res_passive_queue_type                priority_queues
% 2.76/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/1.00  --res_passive_queues_freq               [15;5]
% 2.76/1.00  --res_forward_subs                      full
% 2.76/1.00  --res_backward_subs                     full
% 2.76/1.00  --res_forward_subs_resolution           true
% 2.76/1.00  --res_backward_subs_resolution          true
% 2.76/1.00  --res_orphan_elimination                true
% 2.76/1.00  --res_time_limit                        2.
% 2.76/1.00  --res_out_proof                         true
% 2.76/1.00  
% 2.76/1.00  ------ Superposition Options
% 2.76/1.00  
% 2.76/1.00  --superposition_flag                    true
% 2.76/1.00  --sup_passive_queue_type                priority_queues
% 2.76/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.76/1.00  --demod_completeness_check              fast
% 2.76/1.00  --demod_use_ground                      true
% 2.76/1.00  --sup_to_prop_solver                    passive
% 2.76/1.00  --sup_prop_simpl_new                    true
% 2.76/1.00  --sup_prop_simpl_given                  true
% 2.76/1.00  --sup_fun_splitting                     false
% 2.76/1.00  --sup_smt_interval                      50000
% 2.76/1.00  
% 2.76/1.00  ------ Superposition Simplification Setup
% 2.76/1.00  
% 2.76/1.00  --sup_indices_passive                   []
% 2.76/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.00  --sup_full_bw                           [BwDemod]
% 2.76/1.00  --sup_immed_triv                        [TrivRules]
% 2.76/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.00  --sup_immed_bw_main                     []
% 2.76/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.00  
% 2.76/1.00  ------ Combination Options
% 2.76/1.00  
% 2.76/1.00  --comb_res_mult                         3
% 2.76/1.00  --comb_sup_mult                         2
% 2.76/1.00  --comb_inst_mult                        10
% 2.76/1.00  
% 2.76/1.00  ------ Debug Options
% 2.76/1.00  
% 2.76/1.00  --dbg_backtrace                         false
% 2.76/1.00  --dbg_dump_prop_clauses                 false
% 2.76/1.00  --dbg_dump_prop_clauses_file            -
% 2.76/1.00  --dbg_out_stat                          false
% 2.76/1.00  ------ Parsing...
% 2.76/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.76/1.00  
% 2.76/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.76/1.00  
% 2.76/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.76/1.00  
% 2.76/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.76/1.00  ------ Proving...
% 2.76/1.00  ------ Problem Properties 
% 2.76/1.00  
% 2.76/1.00  
% 2.76/1.00  clauses                                 17
% 2.76/1.00  conjectures                             1
% 2.76/1.00  EPR                                     1
% 2.76/1.00  Horn                                    13
% 2.76/1.00  unary                                   3
% 2.76/1.00  binary                                  4
% 2.76/1.00  lits                                    46
% 2.76/1.00  lits eq                                 9
% 2.76/1.00  fd_pure                                 0
% 2.76/1.00  fd_pseudo                               0
% 2.76/1.00  fd_cond                                 3
% 2.76/1.00  fd_pseudo_cond                          0
% 2.76/1.00  AC symbols                              0
% 2.76/1.00  
% 2.76/1.00  ------ Schedule dynamic 5 is on 
% 2.76/1.00  
% 2.76/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.76/1.00  
% 2.76/1.00  
% 2.76/1.00  ------ 
% 2.76/1.00  Current options:
% 2.76/1.00  ------ 
% 2.76/1.00  
% 2.76/1.00  ------ Input Options
% 2.76/1.00  
% 2.76/1.00  --out_options                           all
% 2.76/1.00  --tptp_safe_out                         true
% 2.76/1.00  --problem_path                          ""
% 2.76/1.00  --include_path                          ""
% 2.76/1.00  --clausifier                            res/vclausify_rel
% 2.76/1.00  --clausifier_options                    --mode clausify
% 2.76/1.00  --stdin                                 false
% 2.76/1.00  --stats_out                             all
% 2.76/1.00  
% 2.76/1.00  ------ General Options
% 2.76/1.00  
% 2.76/1.00  --fof                                   false
% 2.76/1.00  --time_out_real                         305.
% 2.76/1.00  --time_out_virtual                      -1.
% 2.76/1.00  --symbol_type_check                     false
% 2.76/1.00  --clausify_out                          false
% 2.76/1.00  --sig_cnt_out                           false
% 2.76/1.00  --trig_cnt_out                          false
% 2.76/1.00  --trig_cnt_out_tolerance                1.
% 2.76/1.00  --trig_cnt_out_sk_spl                   false
% 2.76/1.00  --abstr_cl_out                          false
% 2.76/1.00  
% 2.76/1.00  ------ Global Options
% 2.76/1.00  
% 2.76/1.00  --schedule                              default
% 2.76/1.00  --add_important_lit                     false
% 2.76/1.00  --prop_solver_per_cl                    1000
% 2.76/1.00  --min_unsat_core                        false
% 2.76/1.00  --soft_assumptions                      false
% 2.76/1.00  --soft_lemma_size                       3
% 2.76/1.00  --prop_impl_unit_size                   0
% 2.76/1.00  --prop_impl_unit                        []
% 2.76/1.00  --share_sel_clauses                     true
% 2.76/1.00  --reset_solvers                         false
% 2.76/1.00  --bc_imp_inh                            [conj_cone]
% 2.76/1.00  --conj_cone_tolerance                   3.
% 2.76/1.00  --extra_neg_conj                        none
% 2.76/1.00  --large_theory_mode                     true
% 2.76/1.00  --prolific_symb_bound                   200
% 2.76/1.00  --lt_threshold                          2000
% 2.76/1.00  --clause_weak_htbl                      true
% 2.76/1.00  --gc_record_bc_elim                     false
% 2.76/1.00  
% 2.76/1.00  ------ Preprocessing Options
% 2.76/1.00  
% 2.76/1.00  --preprocessing_flag                    true
% 2.76/1.00  --time_out_prep_mult                    0.1
% 2.76/1.00  --splitting_mode                        input
% 2.76/1.00  --splitting_grd                         true
% 2.76/1.00  --splitting_cvd                         false
% 2.76/1.00  --splitting_cvd_svl                     false
% 2.76/1.00  --splitting_nvd                         32
% 2.76/1.00  --sub_typing                            true
% 2.76/1.00  --prep_gs_sim                           true
% 2.76/1.00  --prep_unflatten                        true
% 2.76/1.00  --prep_res_sim                          true
% 2.76/1.00  --prep_upred                            true
% 2.76/1.00  --prep_sem_filter                       exhaustive
% 2.76/1.00  --prep_sem_filter_out                   false
% 2.76/1.00  --pred_elim                             true
% 2.76/1.00  --res_sim_input                         true
% 2.76/1.00  --eq_ax_congr_red                       true
% 2.76/1.00  --pure_diseq_elim                       true
% 2.76/1.00  --brand_transform                       false
% 2.76/1.00  --non_eq_to_eq                          false
% 2.76/1.00  --prep_def_merge                        true
% 2.76/1.00  --prep_def_merge_prop_impl              false
% 2.76/1.00  --prep_def_merge_mbd                    true
% 2.76/1.00  --prep_def_merge_tr_red                 false
% 2.76/1.00  --prep_def_merge_tr_cl                  false
% 2.76/1.00  --smt_preprocessing                     true
% 2.76/1.00  --smt_ac_axioms                         fast
% 2.76/1.00  --preprocessed_out                      false
% 2.76/1.00  --preprocessed_stats                    false
% 2.76/1.00  
% 2.76/1.00  ------ Abstraction refinement Options
% 2.76/1.00  
% 2.76/1.00  --abstr_ref                             []
% 2.76/1.00  --abstr_ref_prep                        false
% 2.76/1.00  --abstr_ref_until_sat                   false
% 2.76/1.00  --abstr_ref_sig_restrict                funpre
% 2.76/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/1.00  --abstr_ref_under                       []
% 2.76/1.00  
% 2.76/1.00  ------ SAT Options
% 2.76/1.00  
% 2.76/1.00  --sat_mode                              false
% 2.76/1.00  --sat_fm_restart_options                ""
% 2.76/1.00  --sat_gr_def                            false
% 2.76/1.00  --sat_epr_types                         true
% 2.76/1.00  --sat_non_cyclic_types                  false
% 2.76/1.00  --sat_finite_models                     false
% 2.76/1.00  --sat_fm_lemmas                         false
% 2.76/1.00  --sat_fm_prep                           false
% 2.76/1.00  --sat_fm_uc_incr                        true
% 2.76/1.00  --sat_out_model                         small
% 2.76/1.00  --sat_out_clauses                       false
% 2.76/1.00  
% 2.76/1.00  ------ QBF Options
% 2.76/1.00  
% 2.76/1.00  --qbf_mode                              false
% 2.76/1.00  --qbf_elim_univ                         false
% 2.76/1.00  --qbf_dom_inst                          none
% 2.76/1.00  --qbf_dom_pre_inst                      false
% 2.76/1.00  --qbf_sk_in                             false
% 2.76/1.00  --qbf_pred_elim                         true
% 2.76/1.00  --qbf_split                             512
% 2.76/1.00  
% 2.76/1.00  ------ BMC1 Options
% 2.76/1.00  
% 2.76/1.00  --bmc1_incremental                      false
% 2.76/1.00  --bmc1_axioms                           reachable_all
% 2.76/1.00  --bmc1_min_bound                        0
% 2.76/1.00  --bmc1_max_bound                        -1
% 2.76/1.00  --bmc1_max_bound_default                -1
% 2.76/1.00  --bmc1_symbol_reachability              true
% 2.76/1.00  --bmc1_property_lemmas                  false
% 2.76/1.00  --bmc1_k_induction                      false
% 2.76/1.00  --bmc1_non_equiv_states                 false
% 2.76/1.00  --bmc1_deadlock                         false
% 2.76/1.00  --bmc1_ucm                              false
% 2.76/1.00  --bmc1_add_unsat_core                   none
% 2.76/1.00  --bmc1_unsat_core_children              false
% 2.76/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/1.00  --bmc1_out_stat                         full
% 2.76/1.00  --bmc1_ground_init                      false
% 2.76/1.00  --bmc1_pre_inst_next_state              false
% 2.76/1.00  --bmc1_pre_inst_state                   false
% 2.76/1.00  --bmc1_pre_inst_reach_state             false
% 2.76/1.00  --bmc1_out_unsat_core                   false
% 2.76/1.00  --bmc1_aig_witness_out                  false
% 2.76/1.00  --bmc1_verbose                          false
% 2.76/1.00  --bmc1_dump_clauses_tptp                false
% 2.76/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.76/1.00  --bmc1_dump_file                        -
% 2.76/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.76/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.76/1.00  --bmc1_ucm_extend_mode                  1
% 2.76/1.00  --bmc1_ucm_init_mode                    2
% 2.76/1.00  --bmc1_ucm_cone_mode                    none
% 2.76/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.76/1.00  --bmc1_ucm_relax_model                  4
% 2.76/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.76/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/1.00  --bmc1_ucm_layered_model                none
% 2.76/1.00  --bmc1_ucm_max_lemma_size               10
% 2.76/1.00  
% 2.76/1.00  ------ AIG Options
% 2.76/1.00  
% 2.76/1.00  --aig_mode                              false
% 2.76/1.00  
% 2.76/1.00  ------ Instantiation Options
% 2.76/1.00  
% 2.76/1.00  --instantiation_flag                    true
% 2.76/1.00  --inst_sos_flag                         false
% 2.76/1.00  --inst_sos_phase                        true
% 2.76/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/1.00  --inst_lit_sel_side                     none
% 2.76/1.00  --inst_solver_per_active                1400
% 2.76/1.00  --inst_solver_calls_frac                1.
% 2.76/1.00  --inst_passive_queue_type               priority_queues
% 2.76/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/1.00  --inst_passive_queues_freq              [25;2]
% 2.76/1.00  --inst_dismatching                      true
% 2.76/1.00  --inst_eager_unprocessed_to_passive     true
% 2.76/1.00  --inst_prop_sim_given                   true
% 2.76/1.00  --inst_prop_sim_new                     false
% 2.76/1.00  --inst_subs_new                         false
% 2.76/1.00  --inst_eq_res_simp                      false
% 2.76/1.00  --inst_subs_given                       false
% 2.76/1.00  --inst_orphan_elimination               true
% 2.76/1.00  --inst_learning_loop_flag               true
% 2.76/1.00  --inst_learning_start                   3000
% 2.76/1.00  --inst_learning_factor                  2
% 2.76/1.00  --inst_start_prop_sim_after_learn       3
% 2.76/1.00  --inst_sel_renew                        solver
% 2.76/1.00  --inst_lit_activity_flag                true
% 2.76/1.00  --inst_restr_to_given                   false
% 2.76/1.00  --inst_activity_threshold               500
% 2.76/1.00  --inst_out_proof                        true
% 2.76/1.00  
% 2.76/1.00  ------ Resolution Options
% 2.76/1.00  
% 2.76/1.00  --resolution_flag                       false
% 2.76/1.00  --res_lit_sel                           adaptive
% 2.76/1.00  --res_lit_sel_side                      none
% 2.76/1.00  --res_ordering                          kbo
% 2.76/1.00  --res_to_prop_solver                    active
% 2.76/1.00  --res_prop_simpl_new                    false
% 2.76/1.00  --res_prop_simpl_given                  true
% 2.76/1.00  --res_passive_queue_type                priority_queues
% 2.76/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/1.00  --res_passive_queues_freq               [15;5]
% 2.76/1.00  --res_forward_subs                      full
% 2.76/1.00  --res_backward_subs                     full
% 2.76/1.00  --res_forward_subs_resolution           true
% 2.76/1.00  --res_backward_subs_resolution          true
% 2.76/1.00  --res_orphan_elimination                true
% 2.76/1.00  --res_time_limit                        2.
% 2.76/1.00  --res_out_proof                         true
% 2.76/1.00  
% 2.76/1.00  ------ Superposition Options
% 2.76/1.00  
% 2.76/1.00  --superposition_flag                    true
% 2.76/1.00  --sup_passive_queue_type                priority_queues
% 2.76/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.76/1.00  --demod_completeness_check              fast
% 2.76/1.01  --demod_use_ground                      true
% 2.76/1.01  --sup_to_prop_solver                    passive
% 2.76/1.01  --sup_prop_simpl_new                    true
% 2.76/1.01  --sup_prop_simpl_given                  true
% 2.76/1.01  --sup_fun_splitting                     false
% 2.76/1.01  --sup_smt_interval                      50000
% 2.76/1.01  
% 2.76/1.01  ------ Superposition Simplification Setup
% 2.76/1.01  
% 2.76/1.01  --sup_indices_passive                   []
% 2.76/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.01  --sup_full_bw                           [BwDemod]
% 2.76/1.01  --sup_immed_triv                        [TrivRules]
% 2.76/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.01  --sup_immed_bw_main                     []
% 2.76/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.01  
% 2.76/1.01  ------ Combination Options
% 2.76/1.01  
% 2.76/1.01  --comb_res_mult                         3
% 2.76/1.01  --comb_sup_mult                         2
% 2.76/1.01  --comb_inst_mult                        10
% 2.76/1.01  
% 2.76/1.01  ------ Debug Options
% 2.76/1.01  
% 2.76/1.01  --dbg_backtrace                         false
% 2.76/1.01  --dbg_dump_prop_clauses                 false
% 2.76/1.01  --dbg_dump_prop_clauses_file            -
% 2.76/1.01  --dbg_out_stat                          false
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  ------ Proving...
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  % SZS status Theorem for theBenchmark.p
% 2.76/1.01  
% 2.76/1.01   Resolution empty clause
% 2.76/1.01  
% 2.76/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.76/1.01  
% 2.76/1.01  fof(f3,axiom,(
% 2.76/1.01    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f16,plain,(
% 2.76/1.01    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.76/1.01    inference(ennf_transformation,[],[f3])).
% 2.76/1.01  
% 2.76/1.01  fof(f29,plain,(
% 2.76/1.01    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 2.76/1.01    introduced(choice_axiom,[])).
% 2.76/1.01  
% 2.76/1.01  fof(f30,plain,(
% 2.76/1.01    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 2.76/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f29])).
% 2.76/1.01  
% 2.76/1.01  fof(f42,plain,(
% 2.76/1.01    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.76/1.01    inference(cnf_transformation,[],[f30])).
% 2.76/1.01  
% 2.76/1.01  fof(f10,axiom,(
% 2.76/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f25,plain,(
% 2.76/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 2.76/1.01    inference(ennf_transformation,[],[f10])).
% 2.76/1.01  
% 2.76/1.01  fof(f26,plain,(
% 2.76/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.76/1.01    inference(flattening,[],[f25])).
% 2.76/1.01  
% 2.76/1.01  fof(f33,plain,(
% 2.76/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.76/1.01    inference(nnf_transformation,[],[f26])).
% 2.76/1.01  
% 2.76/1.01  fof(f34,plain,(
% 2.76/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.76/1.01    inference(rectify,[],[f33])).
% 2.76/1.01  
% 2.76/1.01  fof(f36,plain,(
% 2.76/1.01    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 2.76/1.01    introduced(choice_axiom,[])).
% 2.76/1.01  
% 2.76/1.01  fof(f35,plain,(
% 2.76/1.01    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 2.76/1.01    introduced(choice_axiom,[])).
% 2.76/1.01  
% 2.76/1.01  fof(f37,plain,(
% 2.76/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.76/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).
% 2.76/1.01  
% 2.76/1.01  fof(f53,plain,(
% 2.76/1.01    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f37])).
% 2.76/1.01  
% 2.76/1.01  fof(f11,conjecture,(
% 2.76/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f12,negated_conjecture,(
% 2.76/1.01    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 2.76/1.01    inference(negated_conjecture,[],[f11])).
% 2.76/1.01  
% 2.76/1.01  fof(f27,plain,(
% 2.76/1.01    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.76/1.01    inference(ennf_transformation,[],[f12])).
% 2.76/1.01  
% 2.76/1.01  fof(f28,plain,(
% 2.76/1.01    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.76/1.01    inference(flattening,[],[f27])).
% 2.76/1.01  
% 2.76/1.01  fof(f38,plain,(
% 2.76/1.01    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 2.76/1.01    introduced(choice_axiom,[])).
% 2.76/1.01  
% 2.76/1.01  fof(f39,plain,(
% 2.76/1.01    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 2.76/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f38])).
% 2.76/1.01  
% 2.76/1.01  fof(f62,plain,(
% 2.76/1.01    v5_orders_2(sK3)),
% 2.76/1.01    inference(cnf_transformation,[],[f39])).
% 2.76/1.01  
% 2.76/1.01  fof(f59,plain,(
% 2.76/1.01    ~v2_struct_0(sK3)),
% 2.76/1.01    inference(cnf_transformation,[],[f39])).
% 2.76/1.01  
% 2.76/1.01  fof(f60,plain,(
% 2.76/1.01    v3_orders_2(sK3)),
% 2.76/1.01    inference(cnf_transformation,[],[f39])).
% 2.76/1.01  
% 2.76/1.01  fof(f61,plain,(
% 2.76/1.01    v4_orders_2(sK3)),
% 2.76/1.01    inference(cnf_transformation,[],[f39])).
% 2.76/1.01  
% 2.76/1.01  fof(f63,plain,(
% 2.76/1.01    l1_orders_2(sK3)),
% 2.76/1.01    inference(cnf_transformation,[],[f39])).
% 2.76/1.01  
% 2.76/1.01  fof(f9,axiom,(
% 2.76/1.01    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f24,plain,(
% 2.76/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.76/1.01    inference(ennf_transformation,[],[f9])).
% 2.76/1.01  
% 2.76/1.01  fof(f52,plain,(
% 2.76/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f24])).
% 2.76/1.01  
% 2.76/1.01  fof(f4,axiom,(
% 2.76/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f17,plain,(
% 2.76/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.76/1.01    inference(ennf_transformation,[],[f4])).
% 2.76/1.01  
% 2.76/1.01  fof(f45,plain,(
% 2.76/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f17])).
% 2.76/1.01  
% 2.76/1.01  fof(f1,axiom,(
% 2.76/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f13,plain,(
% 2.76/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.76/1.01    inference(ennf_transformation,[],[f1])).
% 2.76/1.01  
% 2.76/1.01  fof(f14,plain,(
% 2.76/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.76/1.01    inference(flattening,[],[f13])).
% 2.76/1.01  
% 2.76/1.01  fof(f40,plain,(
% 2.76/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f14])).
% 2.76/1.01  
% 2.76/1.01  fof(f55,plain,(
% 2.76/1.01    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f37])).
% 2.76/1.01  
% 2.76/1.01  fof(f6,axiom,(
% 2.76/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f19,plain,(
% 2.76/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.76/1.01    inference(ennf_transformation,[],[f6])).
% 2.76/1.01  
% 2.76/1.01  fof(f31,plain,(
% 2.76/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.76/1.01    inference(nnf_transformation,[],[f19])).
% 2.76/1.01  
% 2.76/1.01  fof(f32,plain,(
% 2.76/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.76/1.01    inference(flattening,[],[f31])).
% 2.76/1.01  
% 2.76/1.01  fof(f48,plain,(
% 2.76/1.01    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f32])).
% 2.76/1.01  
% 2.76/1.01  fof(f65,plain,(
% 2.76/1.01    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.76/1.01    inference(equality_resolution,[],[f48])).
% 2.76/1.01  
% 2.76/1.01  fof(f5,axiom,(
% 2.76/1.01    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f18,plain,(
% 2.76/1.01    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 2.76/1.01    inference(ennf_transformation,[],[f5])).
% 2.76/1.01  
% 2.76/1.01  fof(f46,plain,(
% 2.76/1.01    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f18])).
% 2.76/1.01  
% 2.76/1.01  fof(f7,axiom,(
% 2.76/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f20,plain,(
% 2.76/1.01    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.76/1.01    inference(ennf_transformation,[],[f7])).
% 2.76/1.01  
% 2.76/1.01  fof(f21,plain,(
% 2.76/1.01    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.76/1.01    inference(flattening,[],[f20])).
% 2.76/1.01  
% 2.76/1.01  fof(f50,plain,(
% 2.76/1.01    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f21])).
% 2.76/1.01  
% 2.76/1.01  fof(f8,axiom,(
% 2.76/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f22,plain,(
% 2.76/1.01    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.76/1.01    inference(ennf_transformation,[],[f8])).
% 2.76/1.01  
% 2.76/1.01  fof(f23,plain,(
% 2.76/1.01    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.76/1.01    inference(flattening,[],[f22])).
% 2.76/1.01  
% 2.76/1.01  fof(f51,plain,(
% 2.76/1.01    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f23])).
% 2.76/1.01  
% 2.76/1.01  fof(f2,axiom,(
% 2.76/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.76/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.01  
% 2.76/1.01  fof(f15,plain,(
% 2.76/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.76/1.01    inference(ennf_transformation,[],[f2])).
% 2.76/1.01  
% 2.76/1.01  fof(f41,plain,(
% 2.76/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.76/1.01    inference(cnf_transformation,[],[f15])).
% 2.76/1.01  
% 2.76/1.01  fof(f64,plain,(
% 2.76/1.01    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))),
% 2.76/1.01    inference(cnf_transformation,[],[f39])).
% 2.76/1.01  
% 2.76/1.01  cnf(c_4,plain,
% 2.76/1.01      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.76/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1177,plain,
% 2.76/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_18,plain,
% 2.76/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.76/1.01      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 2.76/1.01      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 2.76/1.01      | v2_struct_0(X1)
% 2.76/1.01      | ~ v3_orders_2(X1)
% 2.76/1.01      | ~ v4_orders_2(X1)
% 2.76/1.01      | ~ v5_orders_2(X1)
% 2.76/1.01      | ~ l1_orders_2(X1) ),
% 2.76/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_21,negated_conjecture,
% 2.76/1.01      ( v5_orders_2(sK3) ),
% 2.76/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_458,plain,
% 2.76/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.76/1.01      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 2.76/1.01      | ~ r2_hidden(X2,a_2_1_orders_2(X1,X0))
% 2.76/1.01      | v2_struct_0(X1)
% 2.76/1.01      | ~ v3_orders_2(X1)
% 2.76/1.01      | ~ v4_orders_2(X1)
% 2.76/1.01      | ~ l1_orders_2(X1)
% 2.76/1.01      | sK3 != X1 ),
% 2.76/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_459,plain,
% 2.76/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.76/1.01      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 2.76/1.01      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0))
% 2.76/1.01      | v2_struct_0(sK3)
% 2.76/1.01      | ~ v3_orders_2(sK3)
% 2.76/1.01      | ~ v4_orders_2(sK3)
% 2.76/1.01      | ~ l1_orders_2(sK3) ),
% 2.76/1.01      inference(unflattening,[status(thm)],[c_458]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_24,negated_conjecture,
% 2.76/1.01      ( ~ v2_struct_0(sK3) ),
% 2.76/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_23,negated_conjecture,
% 2.76/1.01      ( v3_orders_2(sK3) ),
% 2.76/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_22,negated_conjecture,
% 2.76/1.01      ( v4_orders_2(sK3) ),
% 2.76/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_20,negated_conjecture,
% 2.76/1.01      ( l1_orders_2(sK3) ),
% 2.76/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_463,plain,
% 2.76/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.76/1.01      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 2.76/1.01      | ~ r2_hidden(X1,a_2_1_orders_2(sK3,X0)) ),
% 2.76/1.01      inference(global_propositional_subsumption,
% 2.76/1.01                [status(thm)],
% 2.76/1.01                [c_459,c_24,c_23,c_22,c_20]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1174,plain,
% 2.76/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.76/1.01      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) = iProver_top
% 2.76/1.01      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_12,plain,
% 2.76/1.01      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.76/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_5,plain,
% 2.76/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.76/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_301,plain,
% 2.76/1.01      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.76/1.01      inference(resolution,[status(thm)],[c_12,c_5]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_619,plain,
% 2.76/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 2.76/1.01      inference(resolution_lifted,[status(thm)],[c_301,c_20]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_620,plain,
% 2.76/1.01      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 2.76/1.01      inference(unflattening,[status(thm)],[c_619]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1239,plain,
% 2.76/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.76/1.01      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 2.76/1.01      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top ),
% 2.76/1.01      inference(light_normalisation,[status(thm)],[c_1174,c_620]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_0,plain,
% 2.76/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.76/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1181,plain,
% 2.76/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 2.76/1.01      | r2_hidden(X0,X1) = iProver_top
% 2.76/1.01      | v1_xboole_0(X1) = iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1592,plain,
% 2.76/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.76/1.01      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 2.76/1.01      | r2_hidden(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 2.76/1.01      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_1239,c_1181]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_16,plain,
% 2.76/1.01      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 2.76/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.76/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.76/1.01      | ~ r2_hidden(X3,X2)
% 2.76/1.01      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 2.76/1.01      | v2_struct_0(X0)
% 2.76/1.01      | ~ v3_orders_2(X0)
% 2.76/1.01      | ~ v4_orders_2(X0)
% 2.76/1.01      | ~ v5_orders_2(X0)
% 2.76/1.01      | ~ l1_orders_2(X0) ),
% 2.76/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_407,plain,
% 2.76/1.01      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 2.76/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.76/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.76/1.01      | ~ r2_hidden(X3,X2)
% 2.76/1.01      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 2.76/1.01      | v2_struct_0(X0)
% 2.76/1.01      | ~ v3_orders_2(X0)
% 2.76/1.01      | ~ v4_orders_2(X0)
% 2.76/1.01      | ~ l1_orders_2(X0)
% 2.76/1.01      | sK3 != X0 ),
% 2.76/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_408,plain,
% 2.76/1.01      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
% 2.76/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.76/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.76/1.01      | ~ r2_hidden(X2,X1)
% 2.76/1.01      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1))
% 2.76/1.01      | v2_struct_0(sK3)
% 2.76/1.01      | ~ v3_orders_2(sK3)
% 2.76/1.01      | ~ v4_orders_2(sK3)
% 2.76/1.01      | ~ l1_orders_2(sK3) ),
% 2.76/1.01      inference(unflattening,[status(thm)],[c_407]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_412,plain,
% 2.76/1.01      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2)
% 2.76/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.76/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.76/1.01      | ~ r2_hidden(X2,X1)
% 2.76/1.01      | ~ r2_hidden(X0,a_2_1_orders_2(sK3,X1)) ),
% 2.76/1.01      inference(global_propositional_subsumption,
% 2.76/1.01                [status(thm)],
% 2.76/1.01                [c_408,c_24,c_23,c_22,c_20]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1176,plain,
% 2.76/1.01      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
% 2.76/1.01      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 2.76/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.76/1.01      | r2_hidden(X2,X1) != iProver_top
% 2.76/1.01      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_412]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1273,plain,
% 2.76/1.01      ( r2_orders_2(sK3,sK2(X0,sK3,X1),X2) = iProver_top
% 2.76/1.01      | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
% 2.76/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.76/1.01      | r2_hidden(X2,X1) != iProver_top
% 2.76/1.01      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 2.76/1.01      inference(light_normalisation,[status(thm)],[c_1176,c_620]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_8,plain,
% 2.76/1.01      ( ~ r2_orders_2(X0,X1,X1)
% 2.76/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.76/1.01      | ~ l1_orders_2(X0) ),
% 2.76/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_631,plain,
% 2.76/1.01      ( ~ r2_orders_2(X0,X1,X1)
% 2.76/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.76/1.01      | sK3 != X0 ),
% 2.76/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_632,plain,
% 2.76/1.01      ( ~ r2_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.76/1.01      inference(unflattening,[status(thm)],[c_631]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1167,plain,
% 2.76/1.01      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 2.76/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1193,plain,
% 2.76/1.01      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 2.76/1.01      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 2.76/1.01      inference(light_normalisation,[status(thm)],[c_1167,c_620]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_2008,plain,
% 2.76/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.76/1.01      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
% 2.76/1.01      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 2.76/1.01      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_1273,c_1193]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_4693,plain,
% 2.76/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.76/1.01      | r2_hidden(X1,a_2_1_orders_2(sK3,X0)) != iProver_top
% 2.76/1.01      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 2.76/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2008,c_1239]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_4702,plain,
% 2.76/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.76/1.01      | r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.76/1.01      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_1592,c_4693]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_6,plain,
% 2.76/1.01      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.76/1.01      | ~ l1_struct_0(X0) ),
% 2.76/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_290,plain,
% 2.76/1.01      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.76/1.01      | ~ l1_orders_2(X0) ),
% 2.76/1.01      inference(resolution,[status(thm)],[c_12,c_6]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_624,plain,
% 2.76/1.01      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | sK3 != X0 ),
% 2.76/1.01      inference(resolution_lifted,[status(thm)],[c_290,c_20]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_625,plain,
% 2.76/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.76/1.01      inference(unflattening,[status(thm)],[c_624]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1168,plain,
% 2.76/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1186,plain,
% 2.76/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 2.76/1.01      inference(light_normalisation,[status(thm)],[c_1168,c_620]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_10,plain,
% 2.76/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.76/1.01      | v2_struct_0(X1)
% 2.76/1.01      | ~ v3_orders_2(X1)
% 2.76/1.01      | ~ v4_orders_2(X1)
% 2.76/1.01      | ~ v5_orders_2(X1)
% 2.76/1.01      | ~ l1_orders_2(X1)
% 2.76/1.01      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 2.76/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_566,plain,
% 2.76/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.76/1.01      | v2_struct_0(X1)
% 2.76/1.01      | ~ v3_orders_2(X1)
% 2.76/1.01      | ~ v4_orders_2(X1)
% 2.76/1.01      | ~ l1_orders_2(X1)
% 2.76/1.01      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0)
% 2.76/1.01      | sK3 != X1 ),
% 2.76/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_567,plain,
% 2.76/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.76/1.01      | v2_struct_0(sK3)
% 2.76/1.01      | ~ v3_orders_2(sK3)
% 2.76/1.01      | ~ v4_orders_2(sK3)
% 2.76/1.01      | ~ l1_orders_2(sK3)
% 2.76/1.01      | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
% 2.76/1.01      inference(unflattening,[status(thm)],[c_566]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_571,plain,
% 2.76/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.76/1.01      | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
% 2.76/1.01      inference(global_propositional_subsumption,
% 2.76/1.01                [status(thm)],
% 2.76/1.01                [c_567,c_24,c_23,c_22,c_20]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1169,plain,
% 2.76/1.01      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 2.76/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1198,plain,
% 2.76/1.01      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 2.76/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.76/1.01      inference(light_normalisation,[status(thm)],[c_1169,c_620]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1382,plain,
% 2.76/1.01      ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_1186,c_1198]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_4703,plain,
% 2.76/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.76/1.01      | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.76/1.01      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 2.76/1.01      inference(light_normalisation,[status(thm)],[c_4702,c_1382]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_11,plain,
% 2.76/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.76/1.01      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.76/1.01      | v2_struct_0(X1)
% 2.76/1.01      | ~ v3_orders_2(X1)
% 2.76/1.01      | ~ v4_orders_2(X1)
% 2.76/1.01      | ~ v5_orders_2(X1)
% 2.76/1.01      | ~ l1_orders_2(X1) ),
% 2.76/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_548,plain,
% 2.76/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.76/1.01      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.76/1.01      | v2_struct_0(X1)
% 2.76/1.01      | ~ v3_orders_2(X1)
% 2.76/1.01      | ~ v4_orders_2(X1)
% 2.76/1.01      | ~ l1_orders_2(X1)
% 2.76/1.01      | sK3 != X1 ),
% 2.76/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_549,plain,
% 2.76/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.76/1.01      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.76/1.01      | v2_struct_0(sK3)
% 2.76/1.01      | ~ v3_orders_2(sK3)
% 2.76/1.01      | ~ v4_orders_2(sK3)
% 2.76/1.01      | ~ l1_orders_2(sK3) ),
% 2.76/1.01      inference(unflattening,[status(thm)],[c_548]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_553,plain,
% 2.76/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.76/1.01      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.76/1.01      inference(global_propositional_subsumption,
% 2.76/1.01                [status(thm)],
% 2.76/1.01                [c_549,c_24,c_23,c_22,c_20]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1170,plain,
% 2.76/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.76/1.01      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_553]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1209,plain,
% 2.76/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.76/1.01      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 2.76/1.01      inference(light_normalisation,[status(thm)],[c_1170,c_620]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1,plain,
% 2.76/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.76/1.01      | ~ r2_hidden(X2,X0)
% 2.76/1.01      | ~ v1_xboole_0(X1) ),
% 2.76/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1180,plain,
% 2.76/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.76/1.01      | r2_hidden(X2,X0) != iProver_top
% 2.76/1.01      | v1_xboole_0(X1) != iProver_top ),
% 2.76/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_1919,plain,
% 2.76/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.76/1.01      | r2_hidden(X1,k2_orders_2(sK3,X0)) != iProver_top
% 2.76/1.01      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_1209,c_1180]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_2481,plain,
% 2.76/1.01      ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 2.76/1.01      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_1186,c_1919]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_5086,plain,
% 2.76/1.01      ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 2.76/1.01      inference(global_propositional_subsumption,
% 2.76/1.01                [status(thm)],
% 2.76/1.01                [c_4703,c_1186,c_2481]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_5093,plain,
% 2.76/1.01      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 2.76/1.01      inference(superposition,[status(thm)],[c_1177,c_5086]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_19,negated_conjecture,
% 2.76/1.01      ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 2.76/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_5129,plain,
% 2.76/1.01      ( k1_xboole_0 != k1_xboole_0 ),
% 2.76/1.01      inference(demodulation,[status(thm)],[c_5093,c_19]) ).
% 2.76/1.01  
% 2.76/1.01  cnf(c_5130,plain,
% 2.76/1.01      ( $false ),
% 2.76/1.01      inference(equality_resolution_simp,[status(thm)],[c_5129]) ).
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.76/1.01  
% 2.76/1.01  ------                               Statistics
% 2.76/1.01  
% 2.76/1.01  ------ General
% 2.76/1.01  
% 2.76/1.01  abstr_ref_over_cycles:                  0
% 2.76/1.01  abstr_ref_under_cycles:                 0
% 2.76/1.01  gc_basic_clause_elim:                   0
% 2.76/1.01  forced_gc_time:                         0
% 2.76/1.01  parsing_time:                           0.009
% 2.76/1.01  unif_index_cands_time:                  0.
% 2.76/1.01  unif_index_add_time:                    0.
% 2.76/1.01  orderings_time:                         0.
% 2.76/1.01  out_proof_time:                         0.008
% 2.76/1.01  total_time:                             0.196
% 2.76/1.01  num_of_symbols:                         53
% 2.76/1.01  num_of_terms:                           5880
% 2.76/1.01  
% 2.76/1.01  ------ Preprocessing
% 2.76/1.01  
% 2.76/1.01  num_of_splits:                          0
% 2.76/1.01  num_of_split_atoms:                     0
% 2.76/1.01  num_of_reused_defs:                     0
% 2.76/1.01  num_eq_ax_congr_red:                    36
% 2.76/1.01  num_of_sem_filtered_clauses:            1
% 2.76/1.01  num_of_subtypes:                        0
% 2.76/1.01  monotx_restored_types:                  0
% 2.76/1.01  sat_num_of_epr_types:                   0
% 2.76/1.01  sat_num_of_non_cyclic_types:            0
% 2.76/1.01  sat_guarded_non_collapsed_types:        0
% 2.76/1.01  num_pure_diseq_elim:                    0
% 2.76/1.01  simp_replaced_by:                       0
% 2.76/1.01  res_preprocessed:                       101
% 2.76/1.01  prep_upred:                             0
% 2.76/1.01  prep_unflattend:                        25
% 2.76/1.01  smt_new_axioms:                         0
% 2.76/1.01  pred_elim_cands:                        4
% 2.76/1.01  pred_elim:                              7
% 2.76/1.01  pred_elim_cl:                           8
% 2.76/1.01  pred_elim_cycles:                       12
% 2.76/1.01  merged_defs:                            0
% 2.76/1.01  merged_defs_ncl:                        0
% 2.76/1.01  bin_hyper_res:                          0
% 2.76/1.01  prep_cycles:                            4
% 2.76/1.01  pred_elim_time:                         0.012
% 2.76/1.01  splitting_time:                         0.
% 2.76/1.01  sem_filter_time:                        0.
% 2.76/1.01  monotx_time:                            0.001
% 2.76/1.01  subtype_inf_time:                       0.
% 2.76/1.01  
% 2.76/1.01  ------ Problem properties
% 2.76/1.01  
% 2.76/1.01  clauses:                                17
% 2.76/1.01  conjectures:                            1
% 2.76/1.01  epr:                                    1
% 2.76/1.01  horn:                                   13
% 2.76/1.01  ground:                                 3
% 2.76/1.01  unary:                                  3
% 2.76/1.01  binary:                                 4
% 2.76/1.01  lits:                                   46
% 2.76/1.01  lits_eq:                                9
% 2.76/1.01  fd_pure:                                0
% 2.76/1.01  fd_pseudo:                              0
% 2.76/1.01  fd_cond:                                3
% 2.76/1.01  fd_pseudo_cond:                         0
% 2.76/1.01  ac_symbols:                             0
% 2.76/1.01  
% 2.76/1.01  ------ Propositional Solver
% 2.76/1.01  
% 2.76/1.01  prop_solver_calls:                      27
% 2.76/1.01  prop_fast_solver_calls:                 962
% 2.76/1.01  smt_solver_calls:                       0
% 2.76/1.01  smt_fast_solver_calls:                  0
% 2.76/1.01  prop_num_of_clauses:                    2288
% 2.76/1.01  prop_preprocess_simplified:             5566
% 2.76/1.01  prop_fo_subsumed:                       42
% 2.76/1.01  prop_solver_time:                       0.
% 2.76/1.01  smt_solver_time:                        0.
% 2.76/1.01  smt_fast_solver_time:                   0.
% 2.76/1.01  prop_fast_solver_time:                  0.
% 2.76/1.01  prop_unsat_core_time:                   0.
% 2.76/1.01  
% 2.76/1.01  ------ QBF
% 2.76/1.01  
% 2.76/1.01  qbf_q_res:                              0
% 2.76/1.01  qbf_num_tautologies:                    0
% 2.76/1.01  qbf_prep_cycles:                        0
% 2.76/1.01  
% 2.76/1.01  ------ BMC1
% 2.76/1.01  
% 2.76/1.01  bmc1_current_bound:                     -1
% 2.76/1.01  bmc1_last_solved_bound:                 -1
% 2.76/1.01  bmc1_unsat_core_size:                   -1
% 2.76/1.01  bmc1_unsat_core_parents_size:           -1
% 2.76/1.01  bmc1_merge_next_fun:                    0
% 2.76/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.76/1.01  
% 2.76/1.01  ------ Instantiation
% 2.76/1.01  
% 2.76/1.01  inst_num_of_clauses:                    621
% 2.76/1.01  inst_num_in_passive:                    256
% 2.76/1.01  inst_num_in_active:                     303
% 2.76/1.01  inst_num_in_unprocessed:                62
% 2.76/1.01  inst_num_of_loops:                      320
% 2.76/1.01  inst_num_of_learning_restarts:          0
% 2.76/1.01  inst_num_moves_active_passive:          13
% 2.76/1.01  inst_lit_activity:                      0
% 2.76/1.01  inst_lit_activity_moves:                0
% 2.76/1.01  inst_num_tautologies:                   0
% 2.76/1.01  inst_num_prop_implied:                  0
% 2.76/1.01  inst_num_existing_simplified:           0
% 2.76/1.01  inst_num_eq_res_simplified:             0
% 2.76/1.01  inst_num_child_elim:                    0
% 2.76/1.01  inst_num_of_dismatching_blockings:      56
% 2.76/1.01  inst_num_of_non_proper_insts:           417
% 2.76/1.01  inst_num_of_duplicates:                 0
% 2.76/1.01  inst_inst_num_from_inst_to_res:         0
% 2.76/1.01  inst_dismatching_checking_time:         0.
% 2.76/1.01  
% 2.76/1.01  ------ Resolution
% 2.76/1.01  
% 2.76/1.01  res_num_of_clauses:                     0
% 2.76/1.01  res_num_in_passive:                     0
% 2.76/1.01  res_num_in_active:                      0
% 2.76/1.01  res_num_of_loops:                       105
% 2.76/1.01  res_forward_subset_subsumed:            51
% 2.76/1.01  res_backward_subset_subsumed:           0
% 2.76/1.01  res_forward_subsumed:                   0
% 2.76/1.01  res_backward_subsumed:                  0
% 2.76/1.01  res_forward_subsumption_resolution:     3
% 2.76/1.01  res_backward_subsumption_resolution:    0
% 2.76/1.01  res_clause_to_clause_subsumption:       296
% 2.76/1.01  res_orphan_elimination:                 0
% 2.76/1.01  res_tautology_del:                      39
% 2.76/1.01  res_num_eq_res_simplified:              0
% 2.76/1.01  res_num_sel_changes:                    0
% 2.76/1.01  res_moves_from_active_to_pass:          0
% 2.76/1.01  
% 2.76/1.01  ------ Superposition
% 2.76/1.01  
% 2.76/1.01  sup_time_total:                         0.
% 2.76/1.01  sup_time_generating:                    0.
% 2.76/1.01  sup_time_sim_full:                      0.
% 2.76/1.01  sup_time_sim_immed:                     0.
% 2.76/1.01  
% 2.76/1.01  sup_num_of_clauses:                     63
% 2.76/1.01  sup_num_in_active:                      44
% 2.76/1.01  sup_num_in_passive:                     19
% 2.76/1.01  sup_num_of_loops:                       63
% 2.76/1.01  sup_fw_superposition:                   63
% 2.76/1.01  sup_bw_superposition:                   15
% 2.76/1.01  sup_immediate_simplified:               18
% 2.76/1.01  sup_given_eliminated:                   1
% 2.76/1.01  comparisons_done:                       0
% 2.76/1.01  comparisons_avoided:                    6
% 2.76/1.01  
% 2.76/1.01  ------ Simplifications
% 2.76/1.01  
% 2.76/1.01  
% 2.76/1.01  sim_fw_subset_subsumed:                 2
% 2.76/1.01  sim_bw_subset_subsumed:                 3
% 2.76/1.01  sim_fw_subsumed:                        6
% 2.76/1.01  sim_bw_subsumed:                        0
% 2.76/1.01  sim_fw_subsumption_res:                 2
% 2.76/1.01  sim_bw_subsumption_res:                 0
% 2.76/1.01  sim_tautology_del:                      1
% 2.76/1.01  sim_eq_tautology_del:                   0
% 2.76/1.01  sim_eq_res_simp:                        0
% 2.76/1.01  sim_fw_demodulated:                     4
% 2.76/1.01  sim_bw_demodulated:                     18
% 2.76/1.01  sim_light_normalised:                   18
% 2.76/1.01  sim_joinable_taut:                      0
% 2.76/1.01  sim_joinable_simp:                      0
% 2.76/1.01  sim_ac_normalised:                      0
% 2.76/1.01  sim_smt_subsumption:                    0
% 2.76/1.01  
%------------------------------------------------------------------------------
