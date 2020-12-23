%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:09 EST 2020

% Result     : Theorem 46.94s
% Output     : CNFRefutation 46.94s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 323 expanded)
%              Number of clauses        :  100 ( 123 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   16
%              Number of atoms          :  633 (1360 expanded)
%              Number of equality atoms :  141 ( 251 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f40,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3))
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f40])).

fof(f67,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f24])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f38,plain,(
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

fof(f37,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | r2_hidden(sK1(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_orders_2(X1,X2))
      | r2_hidden(sK1(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f61])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
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

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f19])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1602,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),X0)
    | ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2300,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),a_2_1_orders_2(X0,X1))
    | ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),a_2_1_orders_2(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1602])).

cnf(c_117035,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),a_2_1_orders_2(X0,k1_xboole_0))
    | ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),a_2_1_orders_2(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2300])).

cnf(c_117037,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),a_2_1_orders_2(sK3,k1_xboole_0))
    | ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),a_2_1_orders_2(sK3,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_117035])).

cnf(c_482,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_481,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2743,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_482,c_481])).

cnf(c_11,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2756,plain,
    ( ~ l1_struct_0(X0)
    | k1_xboole_0 = k1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2743,c_11])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3476,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_486,c_481])).

cnf(c_62455,plain,
    ( ~ m1_subset_1(k1_struct_0(X0),X1)
    | m1_subset_1(k1_xboole_0,X1)
    | ~ l1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2756,c_3476])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_65327,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ r1_tarski(k1_struct_0(X1),X0)
    | ~ l1_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_62455,c_7])).

cnf(c_483,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2038,plain,
    ( r1_tarski(k1_struct_0(X0),X1)
    | ~ r1_tarski(k1_xboole_0,X1)
    | ~ l1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_483,c_11])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2053,plain,
    ( r1_tarski(k1_struct_0(X0),X1)
    | ~ l1_struct_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2038,c_6])).

cnf(c_66550,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ l1_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_65327,c_2053])).

cnf(c_14,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1453,plain,
    ( l1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_14,c_22])).

cnf(c_69218,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(resolution,[status(thm)],[c_66550,c_1453])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_5124,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | ~ r1_tarski(X2,sK1(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(resolution,[status(thm)],[c_16,c_10])).

cnf(c_50244,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(resolution,[status(thm)],[c_5124,c_6])).

cnf(c_69955,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_69218,c_50244])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_70762,plain,
    ( ~ m1_subset_1(sK0(X0,a_2_1_orders_2(X1,k1_xboole_0)),u1_struct_0(X1))
    | r1_tarski(X0,a_2_1_orders_2(X1,k1_xboole_0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(resolution,[status(thm)],[c_69955,c_0])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2575,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(resolution,[status(thm)],[c_9,c_7])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_6894,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(resolution,[status(thm)],[c_2575,c_5])).

cnf(c_73543,plain,
    ( ~ r2_hidden(sK0(X0,a_2_1_orders_2(X1,k1_xboole_0)),u1_struct_0(X1))
    | r1_tarski(X0,a_2_1_orders_2(X1,k1_xboole_0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(resolution,[status(thm)],[c_70762,c_6894])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_116645,plain,
    ( r1_tarski(u1_struct_0(X0),a_2_1_orders_2(X0,k1_xboole_0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_73543,c_1])).

cnf(c_116647,plain,
    ( r1_tarski(u1_struct_0(sK3),a_2_1_orders_2(sK3,k1_xboole_0))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_116645])).

cnf(c_484,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2279,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),X2)
    | X1 != X2
    | X0 != sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_484])).

cnf(c_9787,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),X0)
    | r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),X1)
    | X1 != X0
    | sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) != sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_2279])).

cnf(c_38774,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),X0)
    | ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),a_2_1_orders_2(X1,X2))
    | X0 != a_2_1_orders_2(X1,X2)
    | sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) != sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_9787])).

cnf(c_110514,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),a_2_1_orders_2(X0,k1_xboole_0))
    | r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),k2_orders_2(sK3,k1_struct_0(sK3)))
    | k2_orders_2(sK3,k1_struct_0(sK3)) != a_2_1_orders_2(X0,k1_xboole_0)
    | sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) != sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_38774])).

cnf(c_110516,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),a_2_1_orders_2(sK3,k1_xboole_0))
    | r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),k2_orders_2(sK3,k1_struct_0(sK3)))
    | k2_orders_2(sK3,k1_struct_0(sK3)) != a_2_1_orders_2(sK3,k1_xboole_0)
    | sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) != sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_110514])).

cnf(c_1487,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_1592,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1487])).

cnf(c_2644,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_orders_2(sK3,k1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_orders_2(sK3,k1_struct_0(sK3)) != X0
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1592])).

cnf(c_13446,plain,
    ( ~ m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_orders_2(sK3,k1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(X0,k1_xboole_0)
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2644])).

cnf(c_13448,plain,
    ( m1_subset_1(k2_orders_2(sK3,k1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(sK3,k1_xboole_0)
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_13446])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_6079,plain,
    ( m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_6081,plain,
    ( m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_6079])).

cnf(c_1764,plain,
    ( X0 != X1
    | k2_orders_2(sK3,k1_struct_0(sK3)) != X1
    | k2_orders_2(sK3,k1_struct_0(sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_2886,plain,
    ( X0 != k2_orders_2(X1,k1_xboole_0)
    | k2_orders_2(sK3,k1_struct_0(sK3)) = X0
    | k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(X1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1764])).

cnf(c_5839,plain,
    ( a_2_1_orders_2(X0,k1_xboole_0) != k2_orders_2(X0,k1_xboole_0)
    | k2_orders_2(sK3,k1_struct_0(sK3)) = a_2_1_orders_2(X0,k1_xboole_0)
    | k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2886])).

cnf(c_5841,plain,
    ( a_2_1_orders_2(sK3,k1_xboole_0) != k2_orders_2(sK3,k1_xboole_0)
    | k2_orders_2(sK3,k1_struct_0(sK3)) = a_2_1_orders_2(sK3,k1_xboole_0)
    | k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5839])).

cnf(c_485,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_4488,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_1146,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1145,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1140,plain,
    ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2176,plain,
    ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_1140])).

cnf(c_3222,plain,
    ( a_2_1_orders_2(X0,k1_xboole_0) = k2_orders_2(X0,k1_xboole_0)
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_2176])).

cnf(c_3251,plain,
    ( a_2_1_orders_2(sK3,k1_xboole_0) = k2_orders_2(sK3,k1_xboole_0)
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3222])).

cnf(c_2376,plain,
    ( sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) = sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_488,plain,
    ( X0 != X1
    | X2 != X3
    | k2_orders_2(X0,X2) = k2_orders_2(X1,X3) ),
    theory(equality)).

cnf(c_1766,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(X0,X1)
    | k1_struct_0(sK3) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_488])).

cnf(c_2133,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(X0,k1_xboole_0)
    | k1_struct_0(sK3) != k1_xboole_0
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1766])).

cnf(c_2135,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(sK3,k1_xboole_0)
    | k1_struct_0(sK3) != k1_xboole_0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2133])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1551,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1888,plain,
    ( ~ m1_subset_1(k2_orders_2(sK3,k1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(k2_orders_2(sK3,k1_struct_0(sK3)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1551])).

cnf(c_1575,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1581,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1575])).

cnf(c_1482,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1574,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(k1_xboole_0,u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_1577,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(k1_xboole_0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1574])).

cnf(c_1525,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),u1_struct_0(sK3))
    | r1_tarski(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1526,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),k2_orders_2(sK3,k1_struct_0(sK3)))
    | r1_tarski(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1434,plain,
    ( ~ r1_tarski(k2_orders_2(sK3,k1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3)))
    | u1_struct_0(sK3) = k2_orders_2(sK3,k1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_489,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_502,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_489])).

cnf(c_82,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_78,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_60,plain,
    ( ~ l1_struct_0(sK3)
    | k1_struct_0(sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_51,plain,
    ( ~ l1_orders_2(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_21,negated_conjecture,
    ( u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_30,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,plain,
    ( v4_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_28,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_117037,c_116647,c_110516,c_13448,c_6081,c_5841,c_4488,c_3251,c_2376,c_2135,c_1888,c_1581,c_1577,c_1525,c_1526,c_1434,c_502,c_82,c_78,c_60,c_51,c_21,c_31,c_22,c_30,c_23,c_29,c_24,c_28,c_25,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 46.94/6.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 46.94/6.50  
% 46.94/6.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 46.94/6.50  
% 46.94/6.50  ------  iProver source info
% 46.94/6.50  
% 46.94/6.50  git: date: 2020-06-30 10:37:57 +0100
% 46.94/6.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 46.94/6.50  git: non_committed_changes: false
% 46.94/6.50  git: last_make_outside_of_git: false
% 46.94/6.50  
% 46.94/6.50  ------ 
% 46.94/6.50  
% 46.94/6.50  ------ Input Options
% 46.94/6.50  
% 46.94/6.50  --out_options                           all
% 46.94/6.50  --tptp_safe_out                         true
% 46.94/6.50  --problem_path                          ""
% 46.94/6.50  --include_path                          ""
% 46.94/6.50  --clausifier                            res/vclausify_rel
% 46.94/6.50  --clausifier_options                    --mode clausify
% 46.94/6.50  --stdin                                 false
% 46.94/6.50  --stats_out                             sel
% 46.94/6.50  
% 46.94/6.50  ------ General Options
% 46.94/6.50  
% 46.94/6.50  --fof                                   false
% 46.94/6.50  --time_out_real                         604.99
% 46.94/6.50  --time_out_virtual                      -1.
% 46.94/6.50  --symbol_type_check                     false
% 46.94/6.50  --clausify_out                          false
% 46.94/6.50  --sig_cnt_out                           false
% 46.94/6.50  --trig_cnt_out                          false
% 46.94/6.50  --trig_cnt_out_tolerance                1.
% 46.94/6.50  --trig_cnt_out_sk_spl                   false
% 46.94/6.50  --abstr_cl_out                          false
% 46.94/6.50  
% 46.94/6.50  ------ Global Options
% 46.94/6.50  
% 46.94/6.50  --schedule                              none
% 46.94/6.50  --add_important_lit                     false
% 46.94/6.50  --prop_solver_per_cl                    1000
% 46.94/6.50  --min_unsat_core                        false
% 46.94/6.50  --soft_assumptions                      false
% 46.94/6.50  --soft_lemma_size                       3
% 46.94/6.50  --prop_impl_unit_size                   0
% 46.94/6.50  --prop_impl_unit                        []
% 46.94/6.50  --share_sel_clauses                     true
% 46.94/6.50  --reset_solvers                         false
% 46.94/6.50  --bc_imp_inh                            [conj_cone]
% 46.94/6.50  --conj_cone_tolerance                   3.
% 46.94/6.50  --extra_neg_conj                        none
% 46.94/6.50  --large_theory_mode                     true
% 46.94/6.50  --prolific_symb_bound                   200
% 46.94/6.50  --lt_threshold                          2000
% 46.94/6.50  --clause_weak_htbl                      true
% 46.94/6.50  --gc_record_bc_elim                     false
% 46.94/6.50  
% 46.94/6.50  ------ Preprocessing Options
% 46.94/6.50  
% 46.94/6.50  --preprocessing_flag                    true
% 46.94/6.50  --time_out_prep_mult                    0.1
% 46.94/6.50  --splitting_mode                        input
% 46.94/6.50  --splitting_grd                         true
% 46.94/6.50  --splitting_cvd                         false
% 46.94/6.50  --splitting_cvd_svl                     false
% 46.94/6.50  --splitting_nvd                         32
% 46.94/6.50  --sub_typing                            true
% 46.94/6.50  --prep_gs_sim                           false
% 46.94/6.50  --prep_unflatten                        true
% 46.94/6.50  --prep_res_sim                          true
% 46.94/6.50  --prep_upred                            true
% 46.94/6.50  --prep_sem_filter                       exhaustive
% 46.94/6.50  --prep_sem_filter_out                   false
% 46.94/6.50  --pred_elim                             false
% 46.94/6.50  --res_sim_input                         true
% 46.94/6.50  --eq_ax_congr_red                       true
% 46.94/6.50  --pure_diseq_elim                       true
% 46.94/6.50  --brand_transform                       false
% 46.94/6.50  --non_eq_to_eq                          false
% 46.94/6.50  --prep_def_merge                        true
% 46.94/6.50  --prep_def_merge_prop_impl              false
% 46.94/6.50  --prep_def_merge_mbd                    true
% 46.94/6.50  --prep_def_merge_tr_red                 false
% 46.94/6.50  --prep_def_merge_tr_cl                  false
% 46.94/6.50  --smt_preprocessing                     true
% 46.94/6.50  --smt_ac_axioms                         fast
% 46.94/6.50  --preprocessed_out                      false
% 46.94/6.50  --preprocessed_stats                    false
% 46.94/6.50  
% 46.94/6.50  ------ Abstraction refinement Options
% 46.94/6.50  
% 46.94/6.50  --abstr_ref                             []
% 46.94/6.50  --abstr_ref_prep                        false
% 46.94/6.50  --abstr_ref_until_sat                   false
% 46.94/6.50  --abstr_ref_sig_restrict                funpre
% 46.94/6.50  --abstr_ref_af_restrict_to_split_sk     false
% 46.94/6.50  --abstr_ref_under                       []
% 46.94/6.50  
% 46.94/6.50  ------ SAT Options
% 46.94/6.50  
% 46.94/6.50  --sat_mode                              false
% 46.94/6.50  --sat_fm_restart_options                ""
% 46.94/6.50  --sat_gr_def                            false
% 46.94/6.50  --sat_epr_types                         true
% 46.94/6.50  --sat_non_cyclic_types                  false
% 46.94/6.50  --sat_finite_models                     false
% 46.94/6.50  --sat_fm_lemmas                         false
% 46.94/6.50  --sat_fm_prep                           false
% 46.94/6.50  --sat_fm_uc_incr                        true
% 46.94/6.50  --sat_out_model                         small
% 46.94/6.50  --sat_out_clauses                       false
% 46.94/6.50  
% 46.94/6.50  ------ QBF Options
% 46.94/6.50  
% 46.94/6.50  --qbf_mode                              false
% 46.94/6.50  --qbf_elim_univ                         false
% 46.94/6.50  --qbf_dom_inst                          none
% 46.94/6.50  --qbf_dom_pre_inst                      false
% 46.94/6.50  --qbf_sk_in                             false
% 46.94/6.50  --qbf_pred_elim                         true
% 46.94/6.50  --qbf_split                             512
% 46.94/6.50  
% 46.94/6.50  ------ BMC1 Options
% 46.94/6.50  
% 46.94/6.50  --bmc1_incremental                      false
% 46.94/6.50  --bmc1_axioms                           reachable_all
% 46.94/6.50  --bmc1_min_bound                        0
% 46.94/6.50  --bmc1_max_bound                        -1
% 46.94/6.50  --bmc1_max_bound_default                -1
% 46.94/6.50  --bmc1_symbol_reachability              true
% 46.94/6.50  --bmc1_property_lemmas                  false
% 46.94/6.50  --bmc1_k_induction                      false
% 46.94/6.50  --bmc1_non_equiv_states                 false
% 46.94/6.50  --bmc1_deadlock                         false
% 46.94/6.50  --bmc1_ucm                              false
% 46.94/6.50  --bmc1_add_unsat_core                   none
% 46.94/6.50  --bmc1_unsat_core_children              false
% 46.94/6.50  --bmc1_unsat_core_extrapolate_axioms    false
% 46.94/6.50  --bmc1_out_stat                         full
% 46.94/6.50  --bmc1_ground_init                      false
% 46.94/6.50  --bmc1_pre_inst_next_state              false
% 46.94/6.50  --bmc1_pre_inst_state                   false
% 46.94/6.50  --bmc1_pre_inst_reach_state             false
% 46.94/6.50  --bmc1_out_unsat_core                   false
% 46.94/6.50  --bmc1_aig_witness_out                  false
% 46.94/6.50  --bmc1_verbose                          false
% 46.94/6.50  --bmc1_dump_clauses_tptp                false
% 46.94/6.50  --bmc1_dump_unsat_core_tptp             false
% 46.94/6.50  --bmc1_dump_file                        -
% 46.94/6.50  --bmc1_ucm_expand_uc_limit              128
% 46.94/6.50  --bmc1_ucm_n_expand_iterations          6
% 46.94/6.50  --bmc1_ucm_extend_mode                  1
% 46.94/6.50  --bmc1_ucm_init_mode                    2
% 46.94/6.50  --bmc1_ucm_cone_mode                    none
% 46.94/6.50  --bmc1_ucm_reduced_relation_type        0
% 46.94/6.50  --bmc1_ucm_relax_model                  4
% 46.94/6.50  --bmc1_ucm_full_tr_after_sat            true
% 46.94/6.50  --bmc1_ucm_expand_neg_assumptions       false
% 46.94/6.50  --bmc1_ucm_layered_model                none
% 46.94/6.50  --bmc1_ucm_max_lemma_size               10
% 46.94/6.50  
% 46.94/6.50  ------ AIG Options
% 46.94/6.50  
% 46.94/6.50  --aig_mode                              false
% 46.94/6.50  
% 46.94/6.50  ------ Instantiation Options
% 46.94/6.50  
% 46.94/6.50  --instantiation_flag                    true
% 46.94/6.50  --inst_sos_flag                         false
% 46.94/6.50  --inst_sos_phase                        true
% 46.94/6.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 46.94/6.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 46.94/6.50  --inst_lit_sel_side                     num_symb
% 46.94/6.50  --inst_solver_per_active                1400
% 46.94/6.50  --inst_solver_calls_frac                1.
% 46.94/6.50  --inst_passive_queue_type               priority_queues
% 46.94/6.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 46.94/6.50  --inst_passive_queues_freq              [25;2]
% 46.94/6.50  --inst_dismatching                      true
% 46.94/6.50  --inst_eager_unprocessed_to_passive     true
% 46.94/6.50  --inst_prop_sim_given                   true
% 46.94/6.50  --inst_prop_sim_new                     false
% 46.94/6.50  --inst_subs_new                         false
% 46.94/6.50  --inst_eq_res_simp                      false
% 46.94/6.50  --inst_subs_given                       false
% 46.94/6.50  --inst_orphan_elimination               true
% 46.94/6.50  --inst_learning_loop_flag               true
% 46.94/6.50  --inst_learning_start                   3000
% 46.94/6.50  --inst_learning_factor                  2
% 46.94/6.50  --inst_start_prop_sim_after_learn       3
% 46.94/6.50  --inst_sel_renew                        solver
% 46.94/6.50  --inst_lit_activity_flag                true
% 46.94/6.50  --inst_restr_to_given                   false
% 46.94/6.50  --inst_activity_threshold               500
% 46.94/6.50  --inst_out_proof                        true
% 46.94/6.50  
% 46.94/6.50  ------ Resolution Options
% 46.94/6.50  
% 46.94/6.50  --resolution_flag                       true
% 46.94/6.50  --res_lit_sel                           adaptive
% 46.94/6.50  --res_lit_sel_side                      none
% 46.94/6.50  --res_ordering                          kbo
% 46.94/6.50  --res_to_prop_solver                    active
% 46.94/6.50  --res_prop_simpl_new                    false
% 46.94/6.50  --res_prop_simpl_given                  true
% 46.94/6.50  --res_passive_queue_type                priority_queues
% 46.94/6.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 46.94/6.50  --res_passive_queues_freq               [15;5]
% 46.94/6.50  --res_forward_subs                      full
% 46.94/6.50  --res_backward_subs                     full
% 46.94/6.50  --res_forward_subs_resolution           true
% 46.94/6.50  --res_backward_subs_resolution          true
% 46.94/6.50  --res_orphan_elimination                true
% 46.94/6.50  --res_time_limit                        2.
% 46.94/6.50  --res_out_proof                         true
% 46.94/6.50  
% 46.94/6.50  ------ Superposition Options
% 46.94/6.50  
% 46.94/6.50  --superposition_flag                    true
% 46.94/6.50  --sup_passive_queue_type                priority_queues
% 46.94/6.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 46.94/6.50  --sup_passive_queues_freq               [1;4]
% 46.94/6.50  --demod_completeness_check              fast
% 46.94/6.50  --demod_use_ground                      true
% 46.94/6.50  --sup_to_prop_solver                    passive
% 46.94/6.50  --sup_prop_simpl_new                    true
% 46.94/6.50  --sup_prop_simpl_given                  true
% 46.94/6.50  --sup_fun_splitting                     false
% 46.94/6.50  --sup_smt_interval                      50000
% 46.94/6.50  
% 46.94/6.50  ------ Superposition Simplification Setup
% 46.94/6.50  
% 46.94/6.50  --sup_indices_passive                   []
% 46.94/6.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 46.94/6.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 46.94/6.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 46.94/6.50  --sup_full_triv                         [TrivRules;PropSubs]
% 46.94/6.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 46.94/6.50  --sup_full_bw                           [BwDemod]
% 46.94/6.50  --sup_immed_triv                        [TrivRules]
% 46.94/6.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 46.94/6.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 46.94/6.50  --sup_immed_bw_main                     []
% 46.94/6.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 46.94/6.50  --sup_input_triv                        [Unflattening;TrivRules]
% 46.94/6.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 46.94/6.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 46.94/6.50  
% 46.94/6.50  ------ Combination Options
% 46.94/6.50  
% 46.94/6.50  --comb_res_mult                         3
% 46.94/6.50  --comb_sup_mult                         2
% 46.94/6.50  --comb_inst_mult                        10
% 46.94/6.50  
% 46.94/6.50  ------ Debug Options
% 46.94/6.50  
% 46.94/6.50  --dbg_backtrace                         false
% 46.94/6.50  --dbg_dump_prop_clauses                 false
% 46.94/6.50  --dbg_dump_prop_clauses_file            -
% 46.94/6.50  --dbg_out_stat                          false
% 46.94/6.50  ------ Parsing...
% 46.94/6.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 46.94/6.50  
% 46.94/6.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 46.94/6.50  
% 46.94/6.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 46.94/6.50  
% 46.94/6.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 46.94/6.50  ------ Proving...
% 46.94/6.50  ------ Problem Properties 
% 46.94/6.50  
% 46.94/6.50  
% 46.94/6.50  clauses                                 26
% 46.94/6.50  conjectures                             6
% 46.94/6.50  EPR                                     11
% 46.94/6.50  Horn                                    17
% 46.94/6.50  unary                                   8
% 46.94/6.50  binary                                  7
% 46.94/6.50  lits                                    98
% 46.94/6.50  lits eq                                 5
% 46.94/6.50  fd_pure                                 0
% 46.94/6.50  fd_pseudo                               0
% 46.94/6.50  fd_cond                                 0
% 46.94/6.50  fd_pseudo_cond                          1
% 46.94/6.50  AC symbols                              0
% 46.94/6.50  
% 46.94/6.50  ------ Input Options Time Limit: Unbounded
% 46.94/6.50  
% 46.94/6.50  
% 46.94/6.50  ------ 
% 46.94/6.50  Current options:
% 46.94/6.50  ------ 
% 46.94/6.50  
% 46.94/6.50  ------ Input Options
% 46.94/6.50  
% 46.94/6.50  --out_options                           all
% 46.94/6.50  --tptp_safe_out                         true
% 46.94/6.50  --problem_path                          ""
% 46.94/6.50  --include_path                          ""
% 46.94/6.50  --clausifier                            res/vclausify_rel
% 46.94/6.50  --clausifier_options                    --mode clausify
% 46.94/6.50  --stdin                                 false
% 46.94/6.50  --stats_out                             sel
% 46.94/6.50  
% 46.94/6.50  ------ General Options
% 46.94/6.50  
% 46.94/6.50  --fof                                   false
% 46.94/6.50  --time_out_real                         604.99
% 46.94/6.50  --time_out_virtual                      -1.
% 46.94/6.50  --symbol_type_check                     false
% 46.94/6.50  --clausify_out                          false
% 46.94/6.50  --sig_cnt_out                           false
% 46.94/6.50  --trig_cnt_out                          false
% 46.94/6.50  --trig_cnt_out_tolerance                1.
% 46.94/6.50  --trig_cnt_out_sk_spl                   false
% 46.94/6.50  --abstr_cl_out                          false
% 46.94/6.50  
% 46.94/6.50  ------ Global Options
% 46.94/6.50  
% 46.94/6.50  --schedule                              none
% 46.94/6.50  --add_important_lit                     false
% 46.94/6.50  --prop_solver_per_cl                    1000
% 46.94/6.50  --min_unsat_core                        false
% 46.94/6.50  --soft_assumptions                      false
% 46.94/6.50  --soft_lemma_size                       3
% 46.94/6.50  --prop_impl_unit_size                   0
% 46.94/6.50  --prop_impl_unit                        []
% 46.94/6.50  --share_sel_clauses                     true
% 46.94/6.50  --reset_solvers                         false
% 46.94/6.50  --bc_imp_inh                            [conj_cone]
% 46.94/6.50  --conj_cone_tolerance                   3.
% 46.94/6.50  --extra_neg_conj                        none
% 46.94/6.50  --large_theory_mode                     true
% 46.94/6.50  --prolific_symb_bound                   200
% 46.94/6.50  --lt_threshold                          2000
% 46.94/6.50  --clause_weak_htbl                      true
% 46.94/6.50  --gc_record_bc_elim                     false
% 46.94/6.50  
% 46.94/6.50  ------ Preprocessing Options
% 46.94/6.50  
% 46.94/6.50  --preprocessing_flag                    true
% 46.94/6.50  --time_out_prep_mult                    0.1
% 46.94/6.50  --splitting_mode                        input
% 46.94/6.50  --splitting_grd                         true
% 46.94/6.50  --splitting_cvd                         false
% 46.94/6.50  --splitting_cvd_svl                     false
% 46.94/6.50  --splitting_nvd                         32
% 46.94/6.50  --sub_typing                            true
% 46.94/6.50  --prep_gs_sim                           false
% 46.94/6.50  --prep_unflatten                        true
% 46.94/6.50  --prep_res_sim                          true
% 46.94/6.50  --prep_upred                            true
% 46.94/6.50  --prep_sem_filter                       exhaustive
% 46.94/6.50  --prep_sem_filter_out                   false
% 46.94/6.50  --pred_elim                             false
% 46.94/6.50  --res_sim_input                         true
% 46.94/6.50  --eq_ax_congr_red                       true
% 46.94/6.50  --pure_diseq_elim                       true
% 46.94/6.50  --brand_transform                       false
% 46.94/6.50  --non_eq_to_eq                          false
% 46.94/6.50  --prep_def_merge                        true
% 46.94/6.50  --prep_def_merge_prop_impl              false
% 46.94/6.50  --prep_def_merge_mbd                    true
% 46.94/6.50  --prep_def_merge_tr_red                 false
% 46.94/6.50  --prep_def_merge_tr_cl                  false
% 46.94/6.50  --smt_preprocessing                     true
% 46.94/6.50  --smt_ac_axioms                         fast
% 46.94/6.50  --preprocessed_out                      false
% 46.94/6.50  --preprocessed_stats                    false
% 46.94/6.50  
% 46.94/6.50  ------ Abstraction refinement Options
% 46.94/6.50  
% 46.94/6.50  --abstr_ref                             []
% 46.94/6.50  --abstr_ref_prep                        false
% 46.94/6.50  --abstr_ref_until_sat                   false
% 46.94/6.50  --abstr_ref_sig_restrict                funpre
% 46.94/6.50  --abstr_ref_af_restrict_to_split_sk     false
% 46.94/6.50  --abstr_ref_under                       []
% 46.94/6.50  
% 46.94/6.50  ------ SAT Options
% 46.94/6.50  
% 46.94/6.50  --sat_mode                              false
% 46.94/6.50  --sat_fm_restart_options                ""
% 46.94/6.50  --sat_gr_def                            false
% 46.94/6.50  --sat_epr_types                         true
% 46.94/6.50  --sat_non_cyclic_types                  false
% 46.94/6.50  --sat_finite_models                     false
% 46.94/6.50  --sat_fm_lemmas                         false
% 46.94/6.50  --sat_fm_prep                           false
% 46.94/6.50  --sat_fm_uc_incr                        true
% 46.94/6.50  --sat_out_model                         small
% 46.94/6.50  --sat_out_clauses                       false
% 46.94/6.50  
% 46.94/6.50  ------ QBF Options
% 46.94/6.50  
% 46.94/6.50  --qbf_mode                              false
% 46.94/6.50  --qbf_elim_univ                         false
% 46.94/6.50  --qbf_dom_inst                          none
% 46.94/6.50  --qbf_dom_pre_inst                      false
% 46.94/6.50  --qbf_sk_in                             false
% 46.94/6.50  --qbf_pred_elim                         true
% 46.94/6.50  --qbf_split                             512
% 46.94/6.50  
% 46.94/6.50  ------ BMC1 Options
% 46.94/6.50  
% 46.94/6.50  --bmc1_incremental                      false
% 46.94/6.50  --bmc1_axioms                           reachable_all
% 46.94/6.50  --bmc1_min_bound                        0
% 46.94/6.50  --bmc1_max_bound                        -1
% 46.94/6.50  --bmc1_max_bound_default                -1
% 46.94/6.50  --bmc1_symbol_reachability              true
% 46.94/6.50  --bmc1_property_lemmas                  false
% 46.94/6.50  --bmc1_k_induction                      false
% 46.94/6.50  --bmc1_non_equiv_states                 false
% 46.94/6.50  --bmc1_deadlock                         false
% 46.94/6.50  --bmc1_ucm                              false
% 46.94/6.50  --bmc1_add_unsat_core                   none
% 46.94/6.50  --bmc1_unsat_core_children              false
% 46.94/6.50  --bmc1_unsat_core_extrapolate_axioms    false
% 46.94/6.50  --bmc1_out_stat                         full
% 46.94/6.50  --bmc1_ground_init                      false
% 46.94/6.50  --bmc1_pre_inst_next_state              false
% 46.94/6.50  --bmc1_pre_inst_state                   false
% 46.94/6.50  --bmc1_pre_inst_reach_state             false
% 46.94/6.50  --bmc1_out_unsat_core                   false
% 46.94/6.50  --bmc1_aig_witness_out                  false
% 46.94/6.50  --bmc1_verbose                          false
% 46.94/6.50  --bmc1_dump_clauses_tptp                false
% 46.94/6.50  --bmc1_dump_unsat_core_tptp             false
% 46.94/6.50  --bmc1_dump_file                        -
% 46.94/6.50  --bmc1_ucm_expand_uc_limit              128
% 46.94/6.50  --bmc1_ucm_n_expand_iterations          6
% 46.94/6.50  --bmc1_ucm_extend_mode                  1
% 46.94/6.50  --bmc1_ucm_init_mode                    2
% 46.94/6.50  --bmc1_ucm_cone_mode                    none
% 46.94/6.50  --bmc1_ucm_reduced_relation_type        0
% 46.94/6.50  --bmc1_ucm_relax_model                  4
% 46.94/6.50  --bmc1_ucm_full_tr_after_sat            true
% 46.94/6.50  --bmc1_ucm_expand_neg_assumptions       false
% 46.94/6.50  --bmc1_ucm_layered_model                none
% 46.94/6.50  --bmc1_ucm_max_lemma_size               10
% 46.94/6.50  
% 46.94/6.50  ------ AIG Options
% 46.94/6.50  
% 46.94/6.50  --aig_mode                              false
% 46.94/6.50  
% 46.94/6.50  ------ Instantiation Options
% 46.94/6.50  
% 46.94/6.50  --instantiation_flag                    true
% 46.94/6.50  --inst_sos_flag                         false
% 46.94/6.50  --inst_sos_phase                        true
% 46.94/6.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 46.94/6.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 46.94/6.50  --inst_lit_sel_side                     num_symb
% 46.94/6.50  --inst_solver_per_active                1400
% 46.94/6.50  --inst_solver_calls_frac                1.
% 46.94/6.50  --inst_passive_queue_type               priority_queues
% 46.94/6.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 46.94/6.50  --inst_passive_queues_freq              [25;2]
% 46.94/6.50  --inst_dismatching                      true
% 46.94/6.50  --inst_eager_unprocessed_to_passive     true
% 46.94/6.50  --inst_prop_sim_given                   true
% 46.94/6.50  --inst_prop_sim_new                     false
% 46.94/6.50  --inst_subs_new                         false
% 46.94/6.50  --inst_eq_res_simp                      false
% 46.94/6.50  --inst_subs_given                       false
% 46.94/6.50  --inst_orphan_elimination               true
% 46.94/6.50  --inst_learning_loop_flag               true
% 46.94/6.50  --inst_learning_start                   3000
% 46.94/6.50  --inst_learning_factor                  2
% 46.94/6.50  --inst_start_prop_sim_after_learn       3
% 46.94/6.50  --inst_sel_renew                        solver
% 46.94/6.50  --inst_lit_activity_flag                true
% 46.94/6.50  --inst_restr_to_given                   false
% 46.94/6.50  --inst_activity_threshold               500
% 46.94/6.50  --inst_out_proof                        true
% 46.94/6.50  
% 46.94/6.50  ------ Resolution Options
% 46.94/6.50  
% 46.94/6.50  --resolution_flag                       true
% 46.94/6.50  --res_lit_sel                           adaptive
% 46.94/6.50  --res_lit_sel_side                      none
% 46.94/6.50  --res_ordering                          kbo
% 46.94/6.50  --res_to_prop_solver                    active
% 46.94/6.50  --res_prop_simpl_new                    false
% 46.94/6.50  --res_prop_simpl_given                  true
% 46.94/6.50  --res_passive_queue_type                priority_queues
% 46.94/6.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 46.94/6.50  --res_passive_queues_freq               [15;5]
% 46.94/6.50  --res_forward_subs                      full
% 46.94/6.50  --res_backward_subs                     full
% 46.94/6.50  --res_forward_subs_resolution           true
% 46.94/6.50  --res_backward_subs_resolution          true
% 46.94/6.50  --res_orphan_elimination                true
% 46.94/6.50  --res_time_limit                        2.
% 46.94/6.50  --res_out_proof                         true
% 46.94/6.50  
% 46.94/6.50  ------ Superposition Options
% 46.94/6.50  
% 46.94/6.50  --superposition_flag                    true
% 46.94/6.50  --sup_passive_queue_type                priority_queues
% 46.94/6.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 46.94/6.50  --sup_passive_queues_freq               [1;4]
% 46.94/6.50  --demod_completeness_check              fast
% 46.94/6.50  --demod_use_ground                      true
% 46.94/6.50  --sup_to_prop_solver                    passive
% 46.94/6.50  --sup_prop_simpl_new                    true
% 46.94/6.50  --sup_prop_simpl_given                  true
% 46.94/6.50  --sup_fun_splitting                     false
% 46.94/6.50  --sup_smt_interval                      50000
% 46.94/6.50  
% 46.94/6.50  ------ Superposition Simplification Setup
% 46.94/6.50  
% 46.94/6.50  --sup_indices_passive                   []
% 46.94/6.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 46.94/6.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 46.94/6.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 46.94/6.50  --sup_full_triv                         [TrivRules;PropSubs]
% 46.94/6.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 46.94/6.50  --sup_full_bw                           [BwDemod]
% 46.94/6.50  --sup_immed_triv                        [TrivRules]
% 46.94/6.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 46.94/6.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 46.94/6.50  --sup_immed_bw_main                     []
% 46.94/6.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 46.94/6.50  --sup_input_triv                        [Unflattening;TrivRules]
% 46.94/6.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 46.94/6.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 46.94/6.50  
% 46.94/6.50  ------ Combination Options
% 46.94/6.50  
% 46.94/6.50  --comb_res_mult                         3
% 46.94/6.50  --comb_sup_mult                         2
% 46.94/6.50  --comb_inst_mult                        10
% 46.94/6.50  
% 46.94/6.50  ------ Debug Options
% 46.94/6.50  
% 46.94/6.50  --dbg_backtrace                         false
% 46.94/6.50  --dbg_dump_prop_clauses                 false
% 46.94/6.50  --dbg_dump_prop_clauses_file            -
% 46.94/6.50  --dbg_out_stat                          false
% 46.94/6.50  
% 46.94/6.50  
% 46.94/6.50  
% 46.94/6.50  
% 46.94/6.50  ------ Proving...
% 46.94/6.50  
% 46.94/6.50  
% 46.94/6.50  % SZS status Theorem for theBenchmark.p
% 46.94/6.50  
% 46.94/6.50  % SZS output start CNFRefutation for theBenchmark.p
% 46.94/6.50  
% 46.94/6.50  fof(f1,axiom,(
% 46.94/6.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 46.94/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f14,plain,(
% 46.94/6.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 46.94/6.50    inference(ennf_transformation,[],[f1])).
% 46.94/6.50  
% 46.94/6.50  fof(f28,plain,(
% 46.94/6.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 46.94/6.50    inference(nnf_transformation,[],[f14])).
% 46.94/6.50  
% 46.94/6.50  fof(f29,plain,(
% 46.94/6.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 46.94/6.50    inference(rectify,[],[f28])).
% 46.94/6.50  
% 46.94/6.50  fof(f30,plain,(
% 46.94/6.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 46.94/6.50    introduced(choice_axiom,[])).
% 46.94/6.50  
% 46.94/6.50  fof(f31,plain,(
% 46.94/6.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 46.94/6.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 46.94/6.50  
% 46.94/6.50  fof(f42,plain,(
% 46.94/6.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f31])).
% 46.94/6.50  
% 46.94/6.50  fof(f7,axiom,(
% 46.94/6.50    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 46.94/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f18,plain,(
% 46.94/6.50    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 46.94/6.50    inference(ennf_transformation,[],[f7])).
% 46.94/6.50  
% 46.94/6.50  fof(f53,plain,(
% 46.94/6.50    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f18])).
% 46.94/6.50  
% 46.94/6.50  fof(f4,axiom,(
% 46.94/6.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 46.94/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f34,plain,(
% 46.94/6.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 46.94/6.50    inference(nnf_transformation,[],[f4])).
% 46.94/6.50  
% 46.94/6.50  fof(f50,plain,(
% 46.94/6.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f34])).
% 46.94/6.50  
% 46.94/6.50  fof(f3,axiom,(
% 46.94/6.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 46.94/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f48,plain,(
% 46.94/6.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f3])).
% 46.94/6.50  
% 46.94/6.50  fof(f10,axiom,(
% 46.94/6.50    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 46.94/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f23,plain,(
% 46.94/6.50    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 46.94/6.50    inference(ennf_transformation,[],[f10])).
% 46.94/6.50  
% 46.94/6.50  fof(f56,plain,(
% 46.94/6.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f23])).
% 46.94/6.50  
% 46.94/6.50  fof(f12,conjecture,(
% 46.94/6.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 46.94/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f13,negated_conjecture,(
% 46.94/6.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 46.94/6.50    inference(negated_conjecture,[],[f12])).
% 46.94/6.50  
% 46.94/6.50  fof(f26,plain,(
% 46.94/6.50    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 46.94/6.50    inference(ennf_transformation,[],[f13])).
% 46.94/6.50  
% 46.94/6.50  fof(f27,plain,(
% 46.94/6.50    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 46.94/6.50    inference(flattening,[],[f26])).
% 46.94/6.50  
% 46.94/6.50  fof(f40,plain,(
% 46.94/6.50    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 46.94/6.50    introduced(choice_axiom,[])).
% 46.94/6.50  
% 46.94/6.50  fof(f41,plain,(
% 46.94/6.50    u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 46.94/6.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f40])).
% 46.94/6.50  
% 46.94/6.50  fof(f67,plain,(
% 46.94/6.50    l1_orders_2(sK3)),
% 46.94/6.50    inference(cnf_transformation,[],[f41])).
% 46.94/6.50  
% 46.94/6.50  fof(f11,axiom,(
% 46.94/6.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 46.94/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f24,plain,(
% 46.94/6.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 46.94/6.50    inference(ennf_transformation,[],[f11])).
% 46.94/6.50  
% 46.94/6.50  fof(f25,plain,(
% 46.94/6.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 46.94/6.50    inference(flattening,[],[f24])).
% 46.94/6.50  
% 46.94/6.50  fof(f35,plain,(
% 46.94/6.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 46.94/6.50    inference(nnf_transformation,[],[f25])).
% 46.94/6.50  
% 46.94/6.50  fof(f36,plain,(
% 46.94/6.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 46.94/6.50    inference(rectify,[],[f35])).
% 46.94/6.50  
% 46.94/6.50  fof(f38,plain,(
% 46.94/6.50    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 46.94/6.50    introduced(choice_axiom,[])).
% 46.94/6.50  
% 46.94/6.50  fof(f37,plain,(
% 46.94/6.50    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 46.94/6.50    introduced(choice_axiom,[])).
% 46.94/6.50  
% 46.94/6.50  fof(f39,plain,(
% 46.94/6.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 46.94/6.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).
% 46.94/6.50  
% 46.94/6.50  fof(f61,plain,(
% 46.94/6.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f39])).
% 46.94/6.50  
% 46.94/6.50  fof(f72,plain,(
% 46.94/6.50    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 46.94/6.50    inference(equality_resolution,[],[f61])).
% 46.94/6.50  
% 46.94/6.50  fof(f6,axiom,(
% 46.94/6.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 46.94/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f17,plain,(
% 46.94/6.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 46.94/6.50    inference(ennf_transformation,[],[f6])).
% 46.94/6.50  
% 46.94/6.50  fof(f52,plain,(
% 46.94/6.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f17])).
% 46.94/6.50  
% 46.94/6.50  fof(f44,plain,(
% 46.94/6.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f31])).
% 46.94/6.50  
% 46.94/6.50  fof(f5,axiom,(
% 46.94/6.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 46.94/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f15,plain,(
% 46.94/6.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 46.94/6.50    inference(ennf_transformation,[],[f5])).
% 46.94/6.50  
% 46.94/6.50  fof(f16,plain,(
% 46.94/6.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 46.94/6.50    inference(flattening,[],[f15])).
% 46.94/6.50  
% 46.94/6.50  fof(f51,plain,(
% 46.94/6.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f16])).
% 46.94/6.50  
% 46.94/6.50  fof(f2,axiom,(
% 46.94/6.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 46.94/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f32,plain,(
% 46.94/6.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 46.94/6.50    inference(nnf_transformation,[],[f2])).
% 46.94/6.50  
% 46.94/6.50  fof(f33,plain,(
% 46.94/6.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 46.94/6.50    inference(flattening,[],[f32])).
% 46.94/6.50  
% 46.94/6.50  fof(f45,plain,(
% 46.94/6.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 46.94/6.50    inference(cnf_transformation,[],[f33])).
% 46.94/6.50  
% 46.94/6.50  fof(f70,plain,(
% 46.94/6.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 46.94/6.50    inference(equality_resolution,[],[f45])).
% 46.94/6.50  
% 46.94/6.50  fof(f43,plain,(
% 46.94/6.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f31])).
% 46.94/6.50  
% 46.94/6.50  fof(f9,axiom,(
% 46.94/6.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 46.94/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f21,plain,(
% 46.94/6.50    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 46.94/6.50    inference(ennf_transformation,[],[f9])).
% 46.94/6.50  
% 46.94/6.50  fof(f22,plain,(
% 46.94/6.50    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 46.94/6.50    inference(flattening,[],[f21])).
% 46.94/6.50  
% 46.94/6.50  fof(f55,plain,(
% 46.94/6.50    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f22])).
% 46.94/6.50  
% 46.94/6.50  fof(f8,axiom,(
% 46.94/6.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 46.94/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f19,plain,(
% 46.94/6.50    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 46.94/6.50    inference(ennf_transformation,[],[f8])).
% 46.94/6.50  
% 46.94/6.50  fof(f20,plain,(
% 46.94/6.50    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 46.94/6.50    inference(flattening,[],[f19])).
% 46.94/6.50  
% 46.94/6.50  fof(f54,plain,(
% 46.94/6.50    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f20])).
% 46.94/6.50  
% 46.94/6.50  fof(f49,plain,(
% 46.94/6.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 46.94/6.50    inference(cnf_transformation,[],[f34])).
% 46.94/6.50  
% 46.94/6.50  fof(f47,plain,(
% 46.94/6.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f33])).
% 46.94/6.50  
% 46.94/6.50  fof(f68,plain,(
% 46.94/6.50    u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3))),
% 46.94/6.50    inference(cnf_transformation,[],[f41])).
% 46.94/6.50  
% 46.94/6.50  fof(f66,plain,(
% 46.94/6.50    v5_orders_2(sK3)),
% 46.94/6.50    inference(cnf_transformation,[],[f41])).
% 46.94/6.50  
% 46.94/6.50  fof(f65,plain,(
% 46.94/6.50    v4_orders_2(sK3)),
% 46.94/6.50    inference(cnf_transformation,[],[f41])).
% 46.94/6.50  
% 46.94/6.50  fof(f64,plain,(
% 46.94/6.50    v3_orders_2(sK3)),
% 46.94/6.50    inference(cnf_transformation,[],[f41])).
% 46.94/6.50  
% 46.94/6.50  fof(f63,plain,(
% 46.94/6.50    ~v2_struct_0(sK3)),
% 46.94/6.50    inference(cnf_transformation,[],[f41])).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2,plain,
% 46.94/6.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 46.94/6.50      inference(cnf_transformation,[],[f42]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1602,plain,
% 46.94/6.50      ( r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),X0)
% 46.94/6.50      | ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),u1_struct_0(sK3))
% 46.94/6.50      | ~ r1_tarski(u1_struct_0(sK3),X0) ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_2]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2300,plain,
% 46.94/6.50      ( r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),a_2_1_orders_2(X0,X1))
% 46.94/6.50      | ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),u1_struct_0(sK3))
% 46.94/6.50      | ~ r1_tarski(u1_struct_0(sK3),a_2_1_orders_2(X0,X1)) ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_1602]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_117035,plain,
% 46.94/6.50      ( r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),a_2_1_orders_2(X0,k1_xboole_0))
% 46.94/6.50      | ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),u1_struct_0(sK3))
% 46.94/6.50      | ~ r1_tarski(u1_struct_0(sK3),a_2_1_orders_2(X0,k1_xboole_0)) ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_2300]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_117037,plain,
% 46.94/6.50      ( r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),a_2_1_orders_2(sK3,k1_xboole_0))
% 46.94/6.50      | ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),u1_struct_0(sK3))
% 46.94/6.50      | ~ r1_tarski(u1_struct_0(sK3),a_2_1_orders_2(sK3,k1_xboole_0)) ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_117035]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_482,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_481,plain,( X0 = X0 ),theory(equality) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2743,plain,
% 46.94/6.50      ( X0 != X1 | X1 = X0 ),
% 46.94/6.50      inference(resolution,[status(thm)],[c_482,c_481]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_11,plain,
% 46.94/6.50      ( ~ l1_struct_0(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 46.94/6.50      inference(cnf_transformation,[],[f53]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2756,plain,
% 46.94/6.50      ( ~ l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0) ),
% 46.94/6.50      inference(resolution,[status(thm)],[c_2743,c_11]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_486,plain,
% 46.94/6.50      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 46.94/6.50      theory(equality) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_3476,plain,
% 46.94/6.50      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 46.94/6.50      inference(resolution,[status(thm)],[c_486,c_481]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_62455,plain,
% 46.94/6.50      ( ~ m1_subset_1(k1_struct_0(X0),X1)
% 46.94/6.50      | m1_subset_1(k1_xboole_0,X1)
% 46.94/6.50      | ~ l1_struct_0(X0) ),
% 46.94/6.50      inference(resolution,[status(thm)],[c_2756,c_3476]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_7,plain,
% 46.94/6.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 46.94/6.50      inference(cnf_transformation,[],[f50]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_65327,plain,
% 46.94/6.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
% 46.94/6.50      | ~ r1_tarski(k1_struct_0(X1),X0)
% 46.94/6.50      | ~ l1_struct_0(X1) ),
% 46.94/6.50      inference(resolution,[status(thm)],[c_62455,c_7]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_483,plain,
% 46.94/6.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 46.94/6.50      theory(equality) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2038,plain,
% 46.94/6.50      ( r1_tarski(k1_struct_0(X0),X1)
% 46.94/6.50      | ~ r1_tarski(k1_xboole_0,X1)
% 46.94/6.50      | ~ l1_struct_0(X0) ),
% 46.94/6.50      inference(resolution,[status(thm)],[c_483,c_11]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_6,plain,
% 46.94/6.50      ( r1_tarski(k1_xboole_0,X0) ),
% 46.94/6.50      inference(cnf_transformation,[],[f48]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2053,plain,
% 46.94/6.50      ( r1_tarski(k1_struct_0(X0),X1) | ~ l1_struct_0(X0) ),
% 46.94/6.50      inference(forward_subsumption_resolution,
% 46.94/6.50                [status(thm)],
% 46.94/6.50                [c_2038,c_6]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_66550,plain,
% 46.94/6.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | ~ l1_struct_0(X1) ),
% 46.94/6.50      inference(forward_subsumption_resolution,
% 46.94/6.50                [status(thm)],
% 46.94/6.50                [c_65327,c_2053]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_14,plain,
% 46.94/6.50      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 46.94/6.50      inference(cnf_transformation,[],[f56]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_22,negated_conjecture,
% 46.94/6.50      ( l1_orders_2(sK3) ),
% 46.94/6.50      inference(cnf_transformation,[],[f67]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1453,plain,
% 46.94/6.50      ( l1_struct_0(sK3) ),
% 46.94/6.50      inference(resolution,[status(thm)],[c_14,c_22]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_69218,plain,
% 46.94/6.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 46.94/6.50      inference(resolution,[status(thm)],[c_66550,c_1453]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_16,plain,
% 46.94/6.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 46.94/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 46.94/6.50      | r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 46.94/6.50      | r2_hidden(sK1(X1,X2,X0),X2)
% 46.94/6.50      | v2_struct_0(X1)
% 46.94/6.50      | ~ v3_orders_2(X1)
% 46.94/6.50      | ~ v4_orders_2(X1)
% 46.94/6.50      | ~ v5_orders_2(X1)
% 46.94/6.50      | ~ l1_orders_2(X1) ),
% 46.94/6.50      inference(cnf_transformation,[],[f72]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_10,plain,
% 46.94/6.50      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 46.94/6.50      inference(cnf_transformation,[],[f52]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_5124,plain,
% 46.94/6.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 46.94/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 46.94/6.50      | r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 46.94/6.50      | ~ r1_tarski(X2,sK1(X1,X2,X0))
% 46.94/6.50      | v2_struct_0(X1)
% 46.94/6.50      | ~ v3_orders_2(X1)
% 46.94/6.50      | ~ v4_orders_2(X1)
% 46.94/6.50      | ~ v5_orders_2(X1)
% 46.94/6.50      | ~ l1_orders_2(X1) ),
% 46.94/6.50      inference(resolution,[status(thm)],[c_16,c_10]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_50244,plain,
% 46.94/6.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 46.94/6.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
% 46.94/6.50      | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0))
% 46.94/6.50      | v2_struct_0(X1)
% 46.94/6.50      | ~ v3_orders_2(X1)
% 46.94/6.51      | ~ v4_orders_2(X1)
% 46.94/6.51      | ~ v5_orders_2(X1)
% 46.94/6.51      | ~ l1_orders_2(X1) ),
% 46.94/6.51      inference(resolution,[status(thm)],[c_5124,c_6]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_69955,plain,
% 46.94/6.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 46.94/6.51      | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0))
% 46.94/6.51      | v2_struct_0(X1)
% 46.94/6.51      | ~ v3_orders_2(X1)
% 46.94/6.51      | ~ v4_orders_2(X1)
% 46.94/6.51      | ~ v5_orders_2(X1)
% 46.94/6.51      | ~ l1_orders_2(X1) ),
% 46.94/6.51      inference(backward_subsumption_resolution,
% 46.94/6.51                [status(thm)],
% 46.94/6.51                [c_69218,c_50244]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_0,plain,
% 46.94/6.51      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 46.94/6.51      inference(cnf_transformation,[],[f44]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_70762,plain,
% 46.94/6.51      ( ~ m1_subset_1(sK0(X0,a_2_1_orders_2(X1,k1_xboole_0)),u1_struct_0(X1))
% 46.94/6.51      | r1_tarski(X0,a_2_1_orders_2(X1,k1_xboole_0))
% 46.94/6.51      | v2_struct_0(X1)
% 46.94/6.51      | ~ v3_orders_2(X1)
% 46.94/6.51      | ~ v4_orders_2(X1)
% 46.94/6.51      | ~ v5_orders_2(X1)
% 46.94/6.51      | ~ l1_orders_2(X1) ),
% 46.94/6.51      inference(resolution,[status(thm)],[c_69955,c_0]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_9,plain,
% 46.94/6.51      ( m1_subset_1(X0,X1)
% 46.94/6.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 46.94/6.51      | ~ r2_hidden(X0,X2) ),
% 46.94/6.51      inference(cnf_transformation,[],[f51]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_2575,plain,
% 46.94/6.51      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_tarski(X2,X1) ),
% 46.94/6.51      inference(resolution,[status(thm)],[c_9,c_7]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_5,plain,
% 46.94/6.51      ( r1_tarski(X0,X0) ),
% 46.94/6.51      inference(cnf_transformation,[],[f70]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_6894,plain,
% 46.94/6.51      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 46.94/6.51      inference(resolution,[status(thm)],[c_2575,c_5]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_73543,plain,
% 46.94/6.51      ( ~ r2_hidden(sK0(X0,a_2_1_orders_2(X1,k1_xboole_0)),u1_struct_0(X1))
% 46.94/6.51      | r1_tarski(X0,a_2_1_orders_2(X1,k1_xboole_0))
% 46.94/6.51      | v2_struct_0(X1)
% 46.94/6.51      | ~ v3_orders_2(X1)
% 46.94/6.51      | ~ v4_orders_2(X1)
% 46.94/6.51      | ~ v5_orders_2(X1)
% 46.94/6.51      | ~ l1_orders_2(X1) ),
% 46.94/6.51      inference(resolution,[status(thm)],[c_70762,c_6894]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1,plain,
% 46.94/6.51      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 46.94/6.51      inference(cnf_transformation,[],[f43]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_116645,plain,
% 46.94/6.51      ( r1_tarski(u1_struct_0(X0),a_2_1_orders_2(X0,k1_xboole_0))
% 46.94/6.51      | v2_struct_0(X0)
% 46.94/6.51      | ~ v3_orders_2(X0)
% 46.94/6.51      | ~ v4_orders_2(X0)
% 46.94/6.51      | ~ v5_orders_2(X0)
% 46.94/6.51      | ~ l1_orders_2(X0) ),
% 46.94/6.51      inference(resolution,[status(thm)],[c_73543,c_1]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_116647,plain,
% 46.94/6.51      ( r1_tarski(u1_struct_0(sK3),a_2_1_orders_2(sK3,k1_xboole_0))
% 46.94/6.51      | v2_struct_0(sK3)
% 46.94/6.51      | ~ v3_orders_2(sK3)
% 46.94/6.51      | ~ v4_orders_2(sK3)
% 46.94/6.51      | ~ v5_orders_2(sK3)
% 46.94/6.51      | ~ l1_orders_2(sK3) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_116645]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_484,plain,
% 46.94/6.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 46.94/6.51      theory(equality) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_2279,plain,
% 46.94/6.51      ( r2_hidden(X0,X1)
% 46.94/6.51      | ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),X2)
% 46.94/6.51      | X1 != X2
% 46.94/6.51      | X0 != sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_484]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_9787,plain,
% 46.94/6.51      ( ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),X0)
% 46.94/6.51      | r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),X1)
% 46.94/6.51      | X1 != X0
% 46.94/6.51      | sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) != sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_2279]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_38774,plain,
% 46.94/6.51      ( r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),X0)
% 46.94/6.51      | ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),a_2_1_orders_2(X1,X2))
% 46.94/6.51      | X0 != a_2_1_orders_2(X1,X2)
% 46.94/6.51      | sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) != sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_9787]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_110514,plain,
% 46.94/6.51      ( ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),a_2_1_orders_2(X0,k1_xboole_0))
% 46.94/6.51      | r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),k2_orders_2(sK3,k1_struct_0(sK3)))
% 46.94/6.51      | k2_orders_2(sK3,k1_struct_0(sK3)) != a_2_1_orders_2(X0,k1_xboole_0)
% 46.94/6.51      | sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) != sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_38774]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_110516,plain,
% 46.94/6.51      ( ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),a_2_1_orders_2(sK3,k1_xboole_0))
% 46.94/6.51      | r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),k2_orders_2(sK3,k1_struct_0(sK3)))
% 46.94/6.51      | k2_orders_2(sK3,k1_struct_0(sK3)) != a_2_1_orders_2(sK3,k1_xboole_0)
% 46.94/6.51      | sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) != sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_110514]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1487,plain,
% 46.94/6.51      ( m1_subset_1(X0,X1)
% 46.94/6.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 46.94/6.51      | X0 != X2
% 46.94/6.51      | X1 != k1_zfmisc_1(X3) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_486]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1592,plain,
% 46.94/6.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 46.94/6.51      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 46.94/6.51      | X2 != X0
% 46.94/6.51      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_1487]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_2644,plain,
% 46.94/6.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 46.94/6.51      | m1_subset_1(k2_orders_2(sK3,k1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 46.94/6.51      | k2_orders_2(sK3,k1_struct_0(sK3)) != X0
% 46.94/6.51      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_1592]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_13446,plain,
% 46.94/6.51      ( ~ m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
% 46.94/6.51      | m1_subset_1(k2_orders_2(sK3,k1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 46.94/6.51      | k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(X0,k1_xboole_0)
% 46.94/6.51      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_2644]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_13448,plain,
% 46.94/6.51      ( m1_subset_1(k2_orders_2(sK3,k1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 46.94/6.51      | ~ m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
% 46.94/6.51      | k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(sK3,k1_xboole_0)
% 46.94/6.51      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_13446]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_13,plain,
% 46.94/6.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 46.94/6.51      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 46.94/6.51      | v2_struct_0(X1)
% 46.94/6.51      | ~ v3_orders_2(X1)
% 46.94/6.51      | ~ v4_orders_2(X1)
% 46.94/6.51      | ~ v5_orders_2(X1)
% 46.94/6.51      | ~ l1_orders_2(X1) ),
% 46.94/6.51      inference(cnf_transformation,[],[f55]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_6079,plain,
% 46.94/6.51      ( m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
% 46.94/6.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 46.94/6.51      | v2_struct_0(X0)
% 46.94/6.51      | ~ v3_orders_2(X0)
% 46.94/6.51      | ~ v4_orders_2(X0)
% 46.94/6.51      | ~ v5_orders_2(X0)
% 46.94/6.51      | ~ l1_orders_2(X0) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_13]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_6081,plain,
% 46.94/6.51      ( m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
% 46.94/6.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 46.94/6.51      | v2_struct_0(sK3)
% 46.94/6.51      | ~ v3_orders_2(sK3)
% 46.94/6.51      | ~ v4_orders_2(sK3)
% 46.94/6.51      | ~ v5_orders_2(sK3)
% 46.94/6.51      | ~ l1_orders_2(sK3) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_6079]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1764,plain,
% 46.94/6.51      ( X0 != X1
% 46.94/6.51      | k2_orders_2(sK3,k1_struct_0(sK3)) != X1
% 46.94/6.51      | k2_orders_2(sK3,k1_struct_0(sK3)) = X0 ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_482]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_2886,plain,
% 46.94/6.51      ( X0 != k2_orders_2(X1,k1_xboole_0)
% 46.94/6.51      | k2_orders_2(sK3,k1_struct_0(sK3)) = X0
% 46.94/6.51      | k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(X1,k1_xboole_0) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_1764]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_5839,plain,
% 46.94/6.51      ( a_2_1_orders_2(X0,k1_xboole_0) != k2_orders_2(X0,k1_xboole_0)
% 46.94/6.51      | k2_orders_2(sK3,k1_struct_0(sK3)) = a_2_1_orders_2(X0,k1_xboole_0)
% 46.94/6.51      | k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(X0,k1_xboole_0) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_2886]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_5841,plain,
% 46.94/6.51      ( a_2_1_orders_2(sK3,k1_xboole_0) != k2_orders_2(sK3,k1_xboole_0)
% 46.94/6.51      | k2_orders_2(sK3,k1_struct_0(sK3)) = a_2_1_orders_2(sK3,k1_xboole_0)
% 46.94/6.51      | k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(sK3,k1_xboole_0) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_5839]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_485,plain,
% 46.94/6.51      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 46.94/6.51      theory(equality) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_4488,plain,
% 46.94/6.51      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 46.94/6.51      | k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_485]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1146,plain,
% 46.94/6.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 46.94/6.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1145,plain,
% 46.94/6.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 46.94/6.51      | r1_tarski(X0,X1) != iProver_top ),
% 46.94/6.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_12,plain,
% 46.94/6.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 46.94/6.51      | v2_struct_0(X1)
% 46.94/6.51      | ~ v3_orders_2(X1)
% 46.94/6.51      | ~ v4_orders_2(X1)
% 46.94/6.51      | ~ v5_orders_2(X1)
% 46.94/6.51      | ~ l1_orders_2(X1)
% 46.94/6.51      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 46.94/6.51      inference(cnf_transformation,[],[f54]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1140,plain,
% 46.94/6.51      ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
% 46.94/6.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 46.94/6.51      | v2_struct_0(X0) = iProver_top
% 46.94/6.51      | v3_orders_2(X0) != iProver_top
% 46.94/6.51      | v4_orders_2(X0) != iProver_top
% 46.94/6.51      | v5_orders_2(X0) != iProver_top
% 46.94/6.51      | l1_orders_2(X0) != iProver_top ),
% 46.94/6.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_2176,plain,
% 46.94/6.51      ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
% 46.94/6.51      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 46.94/6.51      | v2_struct_0(X0) = iProver_top
% 46.94/6.51      | v3_orders_2(X0) != iProver_top
% 46.94/6.51      | v4_orders_2(X0) != iProver_top
% 46.94/6.51      | v5_orders_2(X0) != iProver_top
% 46.94/6.51      | l1_orders_2(X0) != iProver_top ),
% 46.94/6.51      inference(superposition,[status(thm)],[c_1145,c_1140]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_3222,plain,
% 46.94/6.51      ( a_2_1_orders_2(X0,k1_xboole_0) = k2_orders_2(X0,k1_xboole_0)
% 46.94/6.51      | v2_struct_0(X0) = iProver_top
% 46.94/6.51      | v3_orders_2(X0) != iProver_top
% 46.94/6.51      | v4_orders_2(X0) != iProver_top
% 46.94/6.51      | v5_orders_2(X0) != iProver_top
% 46.94/6.51      | l1_orders_2(X0) != iProver_top ),
% 46.94/6.51      inference(superposition,[status(thm)],[c_1146,c_2176]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_3251,plain,
% 46.94/6.51      ( a_2_1_orders_2(sK3,k1_xboole_0) = k2_orders_2(sK3,k1_xboole_0)
% 46.94/6.51      | v2_struct_0(sK3) = iProver_top
% 46.94/6.51      | v3_orders_2(sK3) != iProver_top
% 46.94/6.51      | v4_orders_2(sK3) != iProver_top
% 46.94/6.51      | v5_orders_2(sK3) != iProver_top
% 46.94/6.51      | l1_orders_2(sK3) != iProver_top ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_3222]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_2376,plain,
% 46.94/6.51      ( sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) = sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_481]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_488,plain,
% 46.94/6.51      ( X0 != X1 | X2 != X3 | k2_orders_2(X0,X2) = k2_orders_2(X1,X3) ),
% 46.94/6.51      theory(equality) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1766,plain,
% 46.94/6.51      ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(X0,X1)
% 46.94/6.51      | k1_struct_0(sK3) != X1
% 46.94/6.51      | sK3 != X0 ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_488]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_2133,plain,
% 46.94/6.51      ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(X0,k1_xboole_0)
% 46.94/6.51      | k1_struct_0(sK3) != k1_xboole_0
% 46.94/6.51      | sK3 != X0 ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_1766]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_2135,plain,
% 46.94/6.51      ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(sK3,k1_xboole_0)
% 46.94/6.51      | k1_struct_0(sK3) != k1_xboole_0
% 46.94/6.51      | sK3 != sK3 ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_2133]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_8,plain,
% 46.94/6.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 46.94/6.51      inference(cnf_transformation,[],[f49]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1551,plain,
% 46.94/6.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 46.94/6.51      | r1_tarski(X0,u1_struct_0(X1)) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_8]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1888,plain,
% 46.94/6.51      ( ~ m1_subset_1(k2_orders_2(sK3,k1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 46.94/6.51      | r1_tarski(k2_orders_2(sK3,k1_struct_0(sK3)),u1_struct_0(sK3)) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_1551]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1575,plain,
% 46.94/6.51      ( r1_tarski(k1_xboole_0,u1_struct_0(X0)) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_6]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1581,plain,
% 46.94/6.51      ( r1_tarski(k1_xboole_0,u1_struct_0(sK3)) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_1575]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1482,plain,
% 46.94/6.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 46.94/6.51      | ~ r1_tarski(X0,u1_struct_0(X1)) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_7]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1574,plain,
% 46.94/6.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 46.94/6.51      | ~ r1_tarski(k1_xboole_0,u1_struct_0(X0)) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_1482]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1577,plain,
% 46.94/6.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 46.94/6.51      | ~ r1_tarski(k1_xboole_0,u1_struct_0(sK3)) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_1574]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1525,plain,
% 46.94/6.51      ( r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),u1_struct_0(sK3))
% 46.94/6.51      | r1_tarski(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_1]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1526,plain,
% 46.94/6.51      ( ~ r2_hidden(sK0(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))),k2_orders_2(sK3,k1_struct_0(sK3)))
% 46.94/6.51      | r1_tarski(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3))) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_0]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_3,plain,
% 46.94/6.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 46.94/6.51      inference(cnf_transformation,[],[f47]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_1434,plain,
% 46.94/6.51      ( ~ r1_tarski(k2_orders_2(sK3,k1_struct_0(sK3)),u1_struct_0(sK3))
% 46.94/6.51      | ~ r1_tarski(u1_struct_0(sK3),k2_orders_2(sK3,k1_struct_0(sK3)))
% 46.94/6.51      | u1_struct_0(sK3) = k2_orders_2(sK3,k1_struct_0(sK3)) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_3]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_489,plain,
% 46.94/6.51      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 46.94/6.51      theory(equality) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_502,plain,
% 46.94/6.51      ( u1_struct_0(sK3) = u1_struct_0(sK3) | sK3 != sK3 ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_489]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_82,plain,
% 46.94/6.51      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_3]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_78,plain,
% 46.94/6.51      ( r1_tarski(sK3,sK3) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_5]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_60,plain,
% 46.94/6.51      ( ~ l1_struct_0(sK3) | k1_struct_0(sK3) = k1_xboole_0 ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_11]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_51,plain,
% 46.94/6.51      ( ~ l1_orders_2(sK3) | l1_struct_0(sK3) ),
% 46.94/6.51      inference(instantiation,[status(thm)],[c_14]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_21,negated_conjecture,
% 46.94/6.51      ( u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) ),
% 46.94/6.51      inference(cnf_transformation,[],[f68]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_31,plain,
% 46.94/6.51      ( l1_orders_2(sK3) = iProver_top ),
% 46.94/6.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_23,negated_conjecture,
% 46.94/6.51      ( v5_orders_2(sK3) ),
% 46.94/6.51      inference(cnf_transformation,[],[f66]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_30,plain,
% 46.94/6.51      ( v5_orders_2(sK3) = iProver_top ),
% 46.94/6.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_24,negated_conjecture,
% 46.94/6.51      ( v4_orders_2(sK3) ),
% 46.94/6.51      inference(cnf_transformation,[],[f65]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_29,plain,
% 46.94/6.51      ( v4_orders_2(sK3) = iProver_top ),
% 46.94/6.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_25,negated_conjecture,
% 46.94/6.51      ( v3_orders_2(sK3) ),
% 46.94/6.51      inference(cnf_transformation,[],[f64]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_28,plain,
% 46.94/6.51      ( v3_orders_2(sK3) = iProver_top ),
% 46.94/6.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_26,negated_conjecture,
% 46.94/6.51      ( ~ v2_struct_0(sK3) ),
% 46.94/6.51      inference(cnf_transformation,[],[f63]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(c_27,plain,
% 46.94/6.51      ( v2_struct_0(sK3) != iProver_top ),
% 46.94/6.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 46.94/6.51  
% 46.94/6.51  cnf(contradiction,plain,
% 46.94/6.51      ( $false ),
% 46.94/6.51      inference(minisat,
% 46.94/6.51                [status(thm)],
% 46.94/6.51                [c_117037,c_116647,c_110516,c_13448,c_6081,c_5841,c_4488,
% 46.94/6.51                 c_3251,c_2376,c_2135,c_1888,c_1581,c_1577,c_1525,c_1526,
% 46.94/6.51                 c_1434,c_502,c_82,c_78,c_60,c_51,c_21,c_31,c_22,c_30,
% 46.94/6.51                 c_23,c_29,c_24,c_28,c_25,c_27,c_26]) ).
% 46.94/6.51  
% 46.94/6.51  
% 46.94/6.51  % SZS output end CNFRefutation for theBenchmark.p
% 46.94/6.51  
% 46.94/6.51  ------                               Statistics
% 46.94/6.51  
% 46.94/6.51  ------ Selected
% 46.94/6.51  
% 46.94/6.51  total_time:                             5.499
% 46.94/6.51  
%------------------------------------------------------------------------------
