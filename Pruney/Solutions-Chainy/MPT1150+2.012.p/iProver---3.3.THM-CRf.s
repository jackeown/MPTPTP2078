%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:07 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 978 expanded)
%              Number of clauses        :  117 ( 286 expanded)
%              Number of leaves         :   21 ( 212 expanded)
%              Depth                    :   23
%              Number of atoms          :  706 (4683 expanded)
%              Number of equality atoms :  218 ( 857 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f39,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4))
      & l1_orders_2(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4))
    & l1_orders_2(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f39])).

fof(f63,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
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

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X6,X5)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,X6,sK3(X0,X1,X2))
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK2(X1,X2,X3),X3)
        & r2_hidden(sK2(X1,X2,X3),X2)
        & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,sK2(X1,X2,X3),X3)
                & r2_hidden(sK2(X1,X2,X3),X2)
                & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,X6,sK3(X0,X1,X2))
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK3(X0,X1,X2) = X0
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f37,f36])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f29])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X1,X6,sK3(X0,X1,X2))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
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

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

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
    inference(nnf_transformation,[],[f15])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1516,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1519,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_655,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_656,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_23,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_656,c_24,c_23,c_22,c_20])).

cnf(c_1508,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_12,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_336,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_12,c_6])).

cnf(c_726,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_336,c_20])).

cnf(c_727,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_1555,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(k2_struct_0(sK4))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1508,c_727])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1520,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2101,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1519,c_1520])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_674,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_678,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_674,c_24,c_23,c_22,c_20])).

cnf(c_1507,plain,
    ( a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_1550,plain,
    ( a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1507,c_727])).

cnf(c_1753,plain,
    ( a_2_0_orders_2(sK4,k1_orders_2(sK4,X0)) = k1_orders_2(sK4,k1_orders_2(sK4,X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1555,c_1550])).

cnf(c_2470,plain,
    ( a_2_0_orders_2(sK4,k1_orders_2(sK4,X0)) = k1_orders_2(sK4,k1_orders_2(sK4,X0))
    | r1_tarski(X0,k2_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_1753])).

cnf(c_2844,plain,
    ( a_2_0_orders_2(sK4,k1_orders_2(sK4,k2_struct_0(sK4))) = k1_orders_2(sK4,k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(superposition,[status(thm)],[c_2101,c_2470])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_586,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3(X2,X1,X0) = X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_587,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | sK3(X1,sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_591,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | sK3(X1,sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_587,c_24,c_23,c_22,c_20])).

cnf(c_1511,plain,
    ( sK3(X0,sK4,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK4,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_1566,plain,
    ( sK3(X0,sK4,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK4,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1511,c_727])).

cnf(c_13924,plain,
    ( sK3(X0,sK4,k1_orders_2(sK4,k2_struct_0(sK4))) = X0
    | m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK4,k1_orders_2(sK4,k2_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2844,c_1566])).

cnf(c_15053,plain,
    ( sK3(X0,sK4,k1_orders_2(sK4,k2_struct_0(sK4))) = X0
    | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK4,k1_orders_2(sK4,k2_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1555,c_13924])).

cnf(c_15478,plain,
    ( sK3(sK0(k1_orders_2(sK4,k1_orders_2(sK4,k2_struct_0(sK4))),X0),sK4,k1_orders_2(sK4,k2_struct_0(sK4))) = sK0(k1_orders_2(sK4,k1_orders_2(sK4,k2_struct_0(sK4))),X0)
    | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | r1_tarski(k1_orders_2(sK4,k1_orders_2(sK4,k2_struct_0(sK4))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1519,c_15053])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_49,plain,
    ( ~ l1_orders_2(sK4)
    | l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_67,plain,
    ( ~ l1_struct_0(sK4)
    | u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1083,plain,
    ( X0 != X1
    | k2_struct_0(X0) = k2_struct_0(X1) ),
    theory(equality)).

cnf(c_1093,plain,
    ( k2_struct_0(sK4) = k2_struct_0(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1083])).

cnf(c_1078,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1101,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1701,plain,
    ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
    | k1_xboole_0 = k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1702,plain,
    ( k1_xboole_0 = k1_orders_2(sK4,k2_struct_0(sK4))
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1701])).

cnf(c_1855,plain,
    ( sK1(k1_orders_2(sK4,k2_struct_0(sK4))) = sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_1079,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_1900,plain,
    ( X0 != X1
    | k2_struct_0(sK4) != X1
    | k2_struct_0(sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_2067,plain,
    ( X0 != k2_struct_0(sK4)
    | k2_struct_0(sK4) = X0
    | k2_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1900])).

cnf(c_2361,plain,
    ( u1_struct_0(sK4) != k2_struct_0(sK4)
    | k2_struct_0(sK4) = u1_struct_0(sK4)
    | k2_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2067])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1785,plain,
    ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X0)
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
    | ~ r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2456,plain,
    ( ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
    | ~ r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1785])).

cnf(c_2459,plain,
    ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4)) = iProver_top
    | r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2456])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1806,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2458,plain,
    ( ~ m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1806])).

cnf(c_2461,plain,
    ( m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2458])).

cnf(c_1081,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2644,plain,
    ( u1_struct_0(sK4) != X0
    | k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_1081])).

cnf(c_3606,plain,
    ( u1_struct_0(sK4) != k2_struct_0(sK4)
    | k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2644])).

cnf(c_1080,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1917,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X2)
    | X1 != X2
    | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_2305,plain,
    ( ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X0)
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X1)
    | X1 != X0
    | sK1(k1_orders_2(sK4,k2_struct_0(sK4))) != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_1917])).

cnf(c_3219,plain,
    ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X0)
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
    | X0 != u1_struct_0(sK4)
    | sK1(k1_orders_2(sK4,k2_struct_0(sK4))) != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2305])).

cnf(c_4392,plain,
    ( ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4))
    | k2_struct_0(sK4) != u1_struct_0(sK4)
    | sK1(k1_orders_2(sK4,k2_struct_0(sK4))) != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_3219])).

cnf(c_4393,plain,
    ( k2_struct_0(sK4) != u1_struct_0(sK4)
    | sK1(k1_orders_2(sK4,k2_struct_0(sK4))) != sK1(k1_orders_2(sK4,k2_struct_0(sK4)))
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4392])).

cnf(c_1082,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1740,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1082])).

cnf(c_1833,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1740])).

cnf(c_2347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | k2_struct_0(sK4) != X0
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1833])).

cnf(c_3814,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4)))
    | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | k2_struct_0(sK4) != X0
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2347])).

cnf(c_6392,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4)))
    | k2_struct_0(sK4) != k2_struct_0(sK4)
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3814])).

cnf(c_6393,plain,
    ( k2_struct_0(sK4) != k2_struct_0(sK4)
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(k2_struct_0(sK4))
    | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6392])).

cnf(c_1517,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2022,plain,
    ( a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0)
    | r1_tarski(X0,k2_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_1550])).

cnf(c_2695,plain,
    ( a_2_0_orders_2(sK4,k2_struct_0(sK4)) = k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(superposition,[status(thm)],[c_2101,c_2022])).

cnf(c_9601,plain,
    ( sK3(X0,sK4,k2_struct_0(sK4)) = X0
    | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK4,k2_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2695,c_1566])).

cnf(c_10457,plain,
    ( sK3(X0,sK4,k2_struct_0(sK4)) = X0
    | r2_hidden(X0,k1_orders_2(sK4,k2_struct_0(sK4))) != iProver_top
    | r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_9601])).

cnf(c_11878,plain,
    ( sK3(X0,sK4,k2_struct_0(sK4)) = X0
    | r2_hidden(X0,k1_orders_2(sK4,k2_struct_0(sK4))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10457,c_2101])).

cnf(c_11883,plain,
    ( sK3(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),sK4,k2_struct_0(sK4)) = sK1(k1_orders_2(sK4,k2_struct_0(sK4)))
    | k1_orders_2(sK4,k2_struct_0(sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1517,c_11878])).

cnf(c_5764,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_1704,plain,
    ( k1_orders_2(sK4,k2_struct_0(sK4)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_10269,plain,
    ( k1_orders_2(sK4,k2_struct_0(sK4)) != k1_xboole_0
    | k1_xboole_0 = k1_orders_2(sK4,k2_struct_0(sK4))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1704])).

cnf(c_11951,plain,
    ( sK3(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),sK4,k2_struct_0(sK4)) = sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11883,c_19,c_5764,c_10269])).

cnf(c_16,plain,
    ( r2_orders_2(X0,X1,sK3(X2,X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_514,plain,
    ( r2_orders_2(X0,X1,sK3(X2,X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_515,plain,
    ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_519,plain,
    ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_515,c_24,c_23,c_22,c_20])).

cnf(c_1514,plain,
    ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK4,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_1607,plain,
    ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2)) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK4)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK4,X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1514,c_727])).

cnf(c_8,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_731,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_732,plain,
    ( ~ r2_orders_2(sK4,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_731])).

cnf(c_1506,plain,
    ( r2_orders_2(sK4,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_1545,plain,
    ( r2_orders_2(sK4,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1506,c_727])).

cnf(c_2110,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(X1,sK4,X0),k2_struct_0(sK4)) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK4,X0)) != iProver_top
    | r2_hidden(sK3(X1,sK4,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1607,c_1545])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_24,c_23,c_22,c_20])).

cnf(c_1512,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK4,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_570])).

cnf(c_1573,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(X1,sK4,X0),k2_struct_0(sK4)) = iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK4,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1512,c_727])).

cnf(c_3131,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK4,X0)) != iProver_top
    | r2_hidden(sK3(X1,sK4,X0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2110,c_1573])).

cnf(c_11958,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,k2_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11951,c_3131])).

cnf(c_11984,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11958,c_2695])).

cnf(c_17434,plain,
    ( m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_17451,plain,
    ( m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17434])).

cnf(c_18086,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15478,c_20,c_19,c_49,c_67,c_1093,c_1101,c_1702,c_1855,c_2361,c_2459,c_2461,c_3606,c_4393,c_6393,c_11984,c_17451])).

cnf(c_18091,plain,
    ( r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_18086])).

cnf(c_18221,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18091,c_2101])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:20:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.78/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.78/1.48  
% 7.78/1.48  ------  iProver source info
% 7.78/1.48  
% 7.78/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.78/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.78/1.48  git: non_committed_changes: false
% 7.78/1.48  git: last_make_outside_of_git: false
% 7.78/1.48  
% 7.78/1.48  ------ 
% 7.78/1.48  ------ Parsing...
% 7.78/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.48  ------ Proving...
% 7.78/1.48  ------ Problem Properties 
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  clauses                                 17
% 7.78/1.48  conjectures                             1
% 7.78/1.48  EPR                                     1
% 7.78/1.48  Horn                                    13
% 7.78/1.48  unary                                   2
% 7.78/1.48  binary                                  8
% 7.78/1.48  lits                                    44
% 7.78/1.48  lits eq                                 5
% 7.78/1.48  fd_pure                                 0
% 7.78/1.48  fd_pseudo                               0
% 7.78/1.48  fd_cond                                 1
% 7.78/1.48  fd_pseudo_cond                          0
% 7.78/1.48  AC symbols                              0
% 7.78/1.48  
% 7.78/1.48  ------ Input Options Time Limit: Unbounded
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  ------ 
% 7.78/1.48  Current options:
% 7.78/1.48  ------ 
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  ------ Proving...
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  % SZS status Theorem for theBenchmark.p
% 7.78/1.48  
% 7.78/1.48   Resolution empty clause
% 7.78/1.48  
% 7.78/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  fof(f3,axiom,(
% 7.78/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.78/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f31,plain,(
% 7.78/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.78/1.48    inference(nnf_transformation,[],[f3])).
% 7.78/1.48  
% 7.78/1.48  fof(f46,plain,(
% 7.78/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f31])).
% 7.78/1.48  
% 7.78/1.48  fof(f1,axiom,(
% 7.78/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.78/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f12,plain,(
% 7.78/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.78/1.48    inference(ennf_transformation,[],[f1])).
% 7.78/1.48  
% 7.78/1.48  fof(f25,plain,(
% 7.78/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.78/1.48    inference(nnf_transformation,[],[f12])).
% 7.78/1.48  
% 7.78/1.48  fof(f26,plain,(
% 7.78/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.78/1.48    inference(rectify,[],[f25])).
% 7.78/1.48  
% 7.78/1.48  fof(f27,plain,(
% 7.78/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.78/1.48    introduced(choice_axiom,[])).
% 7.78/1.48  
% 7.78/1.48  fof(f28,plain,(
% 7.78/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 7.78/1.48  
% 7.78/1.48  fof(f42,plain,(
% 7.78/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f28])).
% 7.78/1.48  
% 7.78/1.48  fof(f7,axiom,(
% 7.78/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.78/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f18,plain,(
% 7.78/1.48    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 7.78/1.48    inference(ennf_transformation,[],[f7])).
% 7.78/1.48  
% 7.78/1.48  fof(f19,plain,(
% 7.78/1.48    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.78/1.48    inference(flattening,[],[f18])).
% 7.78/1.48  
% 7.78/1.48  fof(f52,plain,(
% 7.78/1.48    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f19])).
% 7.78/1.48  
% 7.78/1.48  fof(f10,conjecture,(
% 7.78/1.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 7.78/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f11,negated_conjecture,(
% 7.78/1.48    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 7.78/1.48    inference(negated_conjecture,[],[f10])).
% 7.78/1.48  
% 7.78/1.48  fof(f23,plain,(
% 7.78/1.48    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 7.78/1.48    inference(ennf_transformation,[],[f11])).
% 7.78/1.48  
% 7.78/1.48  fof(f24,plain,(
% 7.78/1.48    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 7.78/1.48    inference(flattening,[],[f23])).
% 7.78/1.48  
% 7.78/1.48  fof(f39,plain,(
% 7.78/1.48    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4))),
% 7.78/1.48    introduced(choice_axiom,[])).
% 7.78/1.48  
% 7.78/1.48  fof(f40,plain,(
% 7.78/1.48    k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4)),
% 7.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f39])).
% 7.78/1.48  
% 7.78/1.48  fof(f63,plain,(
% 7.78/1.48    v5_orders_2(sK4)),
% 7.78/1.48    inference(cnf_transformation,[],[f40])).
% 7.78/1.48  
% 7.78/1.48  fof(f60,plain,(
% 7.78/1.48    ~v2_struct_0(sK4)),
% 7.78/1.48    inference(cnf_transformation,[],[f40])).
% 7.78/1.48  
% 7.78/1.48  fof(f61,plain,(
% 7.78/1.48    v3_orders_2(sK4)),
% 7.78/1.48    inference(cnf_transformation,[],[f40])).
% 7.78/1.48  
% 7.78/1.48  fof(f62,plain,(
% 7.78/1.48    v4_orders_2(sK4)),
% 7.78/1.48    inference(cnf_transformation,[],[f40])).
% 7.78/1.48  
% 7.78/1.48  fof(f64,plain,(
% 7.78/1.48    l1_orders_2(sK4)),
% 7.78/1.48    inference(cnf_transformation,[],[f40])).
% 7.78/1.48  
% 7.78/1.48  fof(f8,axiom,(
% 7.78/1.48    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 7.78/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f20,plain,(
% 7.78/1.48    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 7.78/1.48    inference(ennf_transformation,[],[f8])).
% 7.78/1.48  
% 7.78/1.48  fof(f53,plain,(
% 7.78/1.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f20])).
% 7.78/1.48  
% 7.78/1.48  fof(f4,axiom,(
% 7.78/1.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.78/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f14,plain,(
% 7.78/1.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.78/1.48    inference(ennf_transformation,[],[f4])).
% 7.78/1.48  
% 7.78/1.48  fof(f47,plain,(
% 7.78/1.48    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f14])).
% 7.78/1.48  
% 7.78/1.48  fof(f43,plain,(
% 7.78/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f28])).
% 7.78/1.48  
% 7.78/1.48  fof(f6,axiom,(
% 7.78/1.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 7.78/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f16,plain,(
% 7.78/1.48    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 7.78/1.48    inference(ennf_transformation,[],[f6])).
% 7.78/1.48  
% 7.78/1.48  fof(f17,plain,(
% 7.78/1.48    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.78/1.48    inference(flattening,[],[f16])).
% 7.78/1.48  
% 7.78/1.48  fof(f51,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f17])).
% 7.78/1.48  
% 7.78/1.48  fof(f9,axiom,(
% 7.78/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 7.78/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f21,plain,(
% 7.78/1.48    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 7.78/1.48    inference(ennf_transformation,[],[f9])).
% 7.78/1.48  
% 7.78/1.48  fof(f22,plain,(
% 7.78/1.48    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.78/1.48    inference(flattening,[],[f21])).
% 7.78/1.48  
% 7.78/1.48  fof(f34,plain,(
% 7.78/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.78/1.48    inference(nnf_transformation,[],[f22])).
% 7.78/1.48  
% 7.78/1.48  fof(f35,plain,(
% 7.78/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.78/1.48    inference(rectify,[],[f34])).
% 7.78/1.48  
% 7.78/1.48  fof(f37,plain,(
% 7.78/1.48    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK3(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 7.78/1.48    introduced(choice_axiom,[])).
% 7.78/1.48  
% 7.78/1.48  fof(f36,plain,(
% 7.78/1.48    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK2(X1,X2,X3),X3) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))))),
% 7.78/1.48    introduced(choice_axiom,[])).
% 7.78/1.48  
% 7.78/1.48  fof(f38,plain,(
% 7.78/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK2(X1,X2,X3),X3) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK3(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f37,f36])).
% 7.78/1.48  
% 7.78/1.48  fof(f55,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f38])).
% 7.78/1.48  
% 7.78/1.48  fof(f65,plain,(
% 7.78/1.48    k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4))),
% 7.78/1.48    inference(cnf_transformation,[],[f40])).
% 7.78/1.48  
% 7.78/1.48  fof(f2,axiom,(
% 7.78/1.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.78/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f13,plain,(
% 7.78/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.78/1.48    inference(ennf_transformation,[],[f2])).
% 7.78/1.48  
% 7.78/1.48  fof(f29,plain,(
% 7.78/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 7.78/1.48    introduced(choice_axiom,[])).
% 7.78/1.48  
% 7.78/1.48  fof(f30,plain,(
% 7.78/1.48    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 7.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f29])).
% 7.78/1.48  
% 7.78/1.48  fof(f44,plain,(
% 7.78/1.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 7.78/1.48    inference(cnf_transformation,[],[f30])).
% 7.78/1.48  
% 7.78/1.48  fof(f41,plain,(
% 7.78/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f28])).
% 7.78/1.48  
% 7.78/1.48  fof(f45,plain,(
% 7.78/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.78/1.48    inference(cnf_transformation,[],[f31])).
% 7.78/1.48  
% 7.78/1.48  fof(f56,plain,(
% 7.78/1.48    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK3(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f38])).
% 7.78/1.48  
% 7.78/1.48  fof(f5,axiom,(
% 7.78/1.48    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 7.78/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f15,plain,(
% 7.78/1.48    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.78/1.48    inference(ennf_transformation,[],[f5])).
% 7.78/1.48  
% 7.78/1.48  fof(f32,plain,(
% 7.78/1.48    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.78/1.48    inference(nnf_transformation,[],[f15])).
% 7.78/1.48  
% 7.78/1.48  fof(f33,plain,(
% 7.78/1.48    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.78/1.48    inference(flattening,[],[f32])).
% 7.78/1.48  
% 7.78/1.48  fof(f49,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f33])).
% 7.78/1.48  
% 7.78/1.48  fof(f66,plain,(
% 7.78/1.48    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.78/1.48    inference(equality_resolution,[],[f49])).
% 7.78/1.48  
% 7.78/1.48  fof(f54,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f38])).
% 7.78/1.48  
% 7.78/1.48  cnf(c_4,plain,
% 7.78/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.78/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1516,plain,
% 7.78/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.78/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1,plain,
% 7.78/1.48      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.78/1.48      inference(cnf_transformation,[],[f42]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1519,plain,
% 7.78/1.48      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.78/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_11,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.48      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.48      | v2_struct_0(X1)
% 7.78/1.48      | ~ v3_orders_2(X1)
% 7.78/1.48      | ~ v4_orders_2(X1)
% 7.78/1.48      | ~ v5_orders_2(X1)
% 7.78/1.48      | ~ l1_orders_2(X1) ),
% 7.78/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_21,negated_conjecture,
% 7.78/1.48      ( v5_orders_2(sK4) ),
% 7.78/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_655,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.48      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.48      | v2_struct_0(X1)
% 7.78/1.48      | ~ v3_orders_2(X1)
% 7.78/1.48      | ~ v4_orders_2(X1)
% 7.78/1.48      | ~ l1_orders_2(X1)
% 7.78/1.48      | sK4 != X1 ),
% 7.78/1.48      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_656,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | v2_struct_0(sK4)
% 7.78/1.48      | ~ v3_orders_2(sK4)
% 7.78/1.48      | ~ v4_orders_2(sK4)
% 7.78/1.48      | ~ l1_orders_2(sK4) ),
% 7.78/1.48      inference(unflattening,[status(thm)],[c_655]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_24,negated_conjecture,
% 7.78/1.48      ( ~ v2_struct_0(sK4) ),
% 7.78/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_23,negated_conjecture,
% 7.78/1.48      ( v3_orders_2(sK4) ),
% 7.78/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_22,negated_conjecture,
% 7.78/1.48      ( v4_orders_2(sK4) ),
% 7.78/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_20,negated_conjecture,
% 7.78/1.48      ( l1_orders_2(sK4) ),
% 7.78/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_660,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_656,c_24,c_23,c_22,c_20]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1508,plain,
% 7.78/1.48      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.78/1.48      | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_12,plain,
% 7.78/1.48      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 7.78/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_6,plain,
% 7.78/1.48      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.78/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_336,plain,
% 7.78/1.48      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.78/1.48      inference(resolution,[status(thm)],[c_12,c_6]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_726,plain,
% 7.78/1.48      ( u1_struct_0(X0) = k2_struct_0(X0) | sK4 != X0 ),
% 7.78/1.48      inference(resolution_lifted,[status(thm)],[c_336,c_20]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_727,plain,
% 7.78/1.48      ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 7.78/1.48      inference(unflattening,[status(thm)],[c_726]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1555,plain,
% 7.78/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 7.78/1.48      | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(k2_struct_0(sK4))) = iProver_top ),
% 7.78/1.48      inference(light_normalisation,[status(thm)],[c_1508,c_727]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_0,plain,
% 7.78/1.48      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.78/1.48      inference(cnf_transformation,[],[f43]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1520,plain,
% 7.78/1.48      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.78/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2101,plain,
% 7.78/1.48      ( r1_tarski(X0,X0) = iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_1519,c_1520]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_10,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.48      | v2_struct_0(X1)
% 7.78/1.48      | ~ v3_orders_2(X1)
% 7.78/1.48      | ~ v4_orders_2(X1)
% 7.78/1.48      | ~ v5_orders_2(X1)
% 7.78/1.48      | ~ l1_orders_2(X1)
% 7.78/1.48      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 7.78/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_673,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.48      | v2_struct_0(X1)
% 7.78/1.48      | ~ v3_orders_2(X1)
% 7.78/1.48      | ~ v4_orders_2(X1)
% 7.78/1.48      | ~ l1_orders_2(X1)
% 7.78/1.48      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
% 7.78/1.48      | sK4 != X1 ),
% 7.78/1.48      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_674,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | v2_struct_0(sK4)
% 7.78/1.48      | ~ v3_orders_2(sK4)
% 7.78/1.48      | ~ v4_orders_2(sK4)
% 7.78/1.48      | ~ l1_orders_2(sK4)
% 7.78/1.48      | a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0) ),
% 7.78/1.48      inference(unflattening,[status(thm)],[c_673]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_678,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0) ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_674,c_24,c_23,c_22,c_20]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1507,plain,
% 7.78/1.48      ( a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0)
% 7.78/1.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1550,plain,
% 7.78/1.48      ( a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0)
% 7.78/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
% 7.78/1.48      inference(light_normalisation,[status(thm)],[c_1507,c_727]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1753,plain,
% 7.78/1.48      ( a_2_0_orders_2(sK4,k1_orders_2(sK4,X0)) = k1_orders_2(sK4,k1_orders_2(sK4,X0))
% 7.78/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_1555,c_1550]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2470,plain,
% 7.78/1.48      ( a_2_0_orders_2(sK4,k1_orders_2(sK4,X0)) = k1_orders_2(sK4,k1_orders_2(sK4,X0))
% 7.78/1.48      | r1_tarski(X0,k2_struct_0(sK4)) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_1516,c_1753]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2844,plain,
% 7.78/1.48      ( a_2_0_orders_2(sK4,k1_orders_2(sK4,k2_struct_0(sK4))) = k1_orders_2(sK4,k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_2101,c_2470]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_17,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.48      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 7.78/1.48      | v2_struct_0(X1)
% 7.78/1.48      | ~ v3_orders_2(X1)
% 7.78/1.48      | ~ v4_orders_2(X1)
% 7.78/1.48      | ~ v5_orders_2(X1)
% 7.78/1.48      | ~ l1_orders_2(X1)
% 7.78/1.48      | sK3(X2,X1,X0) = X2 ),
% 7.78/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_586,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.48      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 7.78/1.48      | v2_struct_0(X1)
% 7.78/1.48      | ~ v3_orders_2(X1)
% 7.78/1.48      | ~ v4_orders_2(X1)
% 7.78/1.48      | ~ l1_orders_2(X1)
% 7.78/1.48      | sK3(X2,X1,X0) = X2
% 7.78/1.48      | sK4 != X1 ),
% 7.78/1.48      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_587,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 7.78/1.48      | v2_struct_0(sK4)
% 7.78/1.48      | ~ v3_orders_2(sK4)
% 7.78/1.48      | ~ v4_orders_2(sK4)
% 7.78/1.48      | ~ l1_orders_2(sK4)
% 7.78/1.48      | sK3(X1,sK4,X0) = X1 ),
% 7.78/1.48      inference(unflattening,[status(thm)],[c_586]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_591,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 7.78/1.48      | sK3(X1,sK4,X0) = X1 ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_587,c_24,c_23,c_22,c_20]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1511,plain,
% 7.78/1.48      ( sK3(X0,sK4,X1) = X0
% 7.78/1.48      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.78/1.48      | r2_hidden(X0,a_2_0_orders_2(sK4,X1)) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1566,plain,
% 7.78/1.48      ( sK3(X0,sK4,X1) = X0
% 7.78/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 7.78/1.48      | r2_hidden(X0,a_2_0_orders_2(sK4,X1)) != iProver_top ),
% 7.78/1.48      inference(light_normalisation,[status(thm)],[c_1511,c_727]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_13924,plain,
% 7.78/1.48      ( sK3(X0,sK4,k1_orders_2(sK4,k2_struct_0(sK4))) = X0
% 7.78/1.48      | m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 7.78/1.48      | r2_hidden(X0,k1_orders_2(sK4,k1_orders_2(sK4,k2_struct_0(sK4)))) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_2844,c_1566]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_15053,plain,
% 7.78/1.48      ( sK3(X0,sK4,k1_orders_2(sK4,k2_struct_0(sK4))) = X0
% 7.78/1.48      | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 7.78/1.48      | r2_hidden(X0,k1_orders_2(sK4,k1_orders_2(sK4,k2_struct_0(sK4)))) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_1555,c_13924]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_15478,plain,
% 7.78/1.48      ( sK3(sK0(k1_orders_2(sK4,k1_orders_2(sK4,k2_struct_0(sK4))),X0),sK4,k1_orders_2(sK4,k2_struct_0(sK4))) = sK0(k1_orders_2(sK4,k1_orders_2(sK4,k2_struct_0(sK4))),X0)
% 7.78/1.48      | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 7.78/1.48      | r1_tarski(k1_orders_2(sK4,k1_orders_2(sK4,k2_struct_0(sK4))),X0) = iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_1519,c_15053]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_19,negated_conjecture,
% 7.78/1.48      ( k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) ),
% 7.78/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_49,plain,
% 7.78/1.48      ( ~ l1_orders_2(sK4) | l1_struct_0(sK4) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_67,plain,
% 7.78/1.48      ( ~ l1_struct_0(sK4) | u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1083,plain,
% 7.78/1.48      ( X0 != X1 | k2_struct_0(X0) = k2_struct_0(X1) ),
% 7.78/1.48      theory(equality) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1093,plain,
% 7.78/1.48      ( k2_struct_0(sK4) = k2_struct_0(sK4) | sK4 != sK4 ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1083]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1078,plain,( X0 = X0 ),theory(equality) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1101,plain,
% 7.78/1.48      ( sK4 = sK4 ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1078]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_3,plain,
% 7.78/1.48      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 7.78/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1701,plain,
% 7.78/1.48      ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
% 7.78/1.48      | k1_xboole_0 = k1_orders_2(sK4,k2_struct_0(sK4)) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1702,plain,
% 7.78/1.48      ( k1_xboole_0 = k1_orders_2(sK4,k2_struct_0(sK4))
% 7.78/1.48      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_1701]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1855,plain,
% 7.78/1.48      ( sK1(k1_orders_2(sK4,k2_struct_0(sK4))) = sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1078]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1079,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1900,plain,
% 7.78/1.48      ( X0 != X1 | k2_struct_0(sK4) != X1 | k2_struct_0(sK4) = X0 ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1079]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2067,plain,
% 7.78/1.48      ( X0 != k2_struct_0(sK4)
% 7.78/1.48      | k2_struct_0(sK4) = X0
% 7.78/1.48      | k2_struct_0(sK4) != k2_struct_0(sK4) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1900]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2361,plain,
% 7.78/1.48      ( u1_struct_0(sK4) != k2_struct_0(sK4)
% 7.78/1.48      | k2_struct_0(sK4) = u1_struct_0(sK4)
% 7.78/1.48      | k2_struct_0(sK4) != k2_struct_0(sK4) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_2067]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2,plain,
% 7.78/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.78/1.48      inference(cnf_transformation,[],[f41]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1785,plain,
% 7.78/1.48      ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X0)
% 7.78/1.48      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
% 7.78/1.48      | ~ r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),X0) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2456,plain,
% 7.78/1.48      ( ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
% 7.78/1.48      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
% 7.78/1.48      | ~ r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),u1_struct_0(sK4)) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1785]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2459,plain,
% 7.78/1.48      ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) != iProver_top
% 7.78/1.48      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4)) = iProver_top
% 7.78/1.48      | r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_2456]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_5,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.78/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1806,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | r1_tarski(X0,u1_struct_0(sK4)) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_5]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2458,plain,
% 7.78/1.48      ( ~ m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),u1_struct_0(sK4)) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1806]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2461,plain,
% 7.78/1.48      ( m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.78/1.48      | r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_2458]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1081,plain,
% 7.78/1.48      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 7.78/1.48      theory(equality) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2644,plain,
% 7.78/1.48      ( u1_struct_0(sK4) != X0
% 7.78/1.48      | k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(X0) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1081]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_3606,plain,
% 7.78/1.48      ( u1_struct_0(sK4) != k2_struct_0(sK4)
% 7.78/1.48      | k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(k2_struct_0(sK4)) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_2644]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1080,plain,
% 7.78/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.78/1.48      theory(equality) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1917,plain,
% 7.78/1.48      ( r2_hidden(X0,X1)
% 7.78/1.48      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X2)
% 7.78/1.48      | X1 != X2
% 7.78/1.48      | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1080]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2305,plain,
% 7.78/1.48      ( ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X0)
% 7.78/1.48      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X1)
% 7.78/1.48      | X1 != X0
% 7.78/1.48      | sK1(k1_orders_2(sK4,k2_struct_0(sK4))) != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1917]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_3219,plain,
% 7.78/1.48      ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X0)
% 7.78/1.48      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
% 7.78/1.48      | X0 != u1_struct_0(sK4)
% 7.78/1.48      | sK1(k1_orders_2(sK4,k2_struct_0(sK4))) != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_2305]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_4392,plain,
% 7.78/1.48      ( ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
% 7.78/1.48      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4))
% 7.78/1.48      | k2_struct_0(sK4) != u1_struct_0(sK4)
% 7.78/1.48      | sK1(k1_orders_2(sK4,k2_struct_0(sK4))) != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_3219]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_4393,plain,
% 7.78/1.48      ( k2_struct_0(sK4) != u1_struct_0(sK4)
% 7.78/1.48      | sK1(k1_orders_2(sK4,k2_struct_0(sK4))) != sK1(k1_orders_2(sK4,k2_struct_0(sK4)))
% 7.78/1.48      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4)) != iProver_top
% 7.78/1.48      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_4392]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1082,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.78/1.48      theory(equality) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1740,plain,
% 7.78/1.48      ( m1_subset_1(X0,X1)
% 7.78/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 7.78/1.48      | X0 != X2
% 7.78/1.48      | X1 != k1_zfmisc_1(X3) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1082]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1833,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.78/1.48      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 7.78/1.48      | X2 != X0
% 7.78/1.48      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1740]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2347,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.78/1.48      | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | k2_struct_0(sK4) != X0
% 7.78/1.48      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(X1) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1833]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_3814,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4)))
% 7.78/1.48      | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | k2_struct_0(sK4) != X0
% 7.78/1.48      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(k2_struct_0(sK4)) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_2347]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_6392,plain,
% 7.78/1.48      ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4)))
% 7.78/1.48      | k2_struct_0(sK4) != k2_struct_0(sK4)
% 7.78/1.48      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(k2_struct_0(sK4)) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_3814]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_6393,plain,
% 7.78/1.48      ( k2_struct_0(sK4) != k2_struct_0(sK4)
% 7.78/1.48      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(k2_struct_0(sK4))
% 7.78/1.48      | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 7.78/1.48      | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_6392]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1517,plain,
% 7.78/1.48      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2022,plain,
% 7.78/1.48      ( a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0)
% 7.78/1.48      | r1_tarski(X0,k2_struct_0(sK4)) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_1516,c_1550]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2695,plain,
% 7.78/1.48      ( a_2_0_orders_2(sK4,k2_struct_0(sK4)) = k1_orders_2(sK4,k2_struct_0(sK4)) ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_2101,c_2022]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_9601,plain,
% 7.78/1.48      ( sK3(X0,sK4,k2_struct_0(sK4)) = X0
% 7.78/1.48      | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 7.78/1.48      | r2_hidden(X0,k1_orders_2(sK4,k2_struct_0(sK4))) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_2695,c_1566]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_10457,plain,
% 7.78/1.48      ( sK3(X0,sK4,k2_struct_0(sK4)) = X0
% 7.78/1.48      | r2_hidden(X0,k1_orders_2(sK4,k2_struct_0(sK4))) != iProver_top
% 7.78/1.48      | r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4)) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_1516,c_9601]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_11878,plain,
% 7.78/1.48      ( sK3(X0,sK4,k2_struct_0(sK4)) = X0
% 7.78/1.48      | r2_hidden(X0,k1_orders_2(sK4,k2_struct_0(sK4))) != iProver_top ),
% 7.78/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_10457,c_2101]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_11883,plain,
% 7.78/1.48      ( sK3(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),sK4,k2_struct_0(sK4)) = sK1(k1_orders_2(sK4,k2_struct_0(sK4)))
% 7.78/1.48      | k1_orders_2(sK4,k2_struct_0(sK4)) = k1_xboole_0 ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_1517,c_11878]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_5764,plain,
% 7.78/1.48      ( k1_xboole_0 = k1_xboole_0 ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1078]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1704,plain,
% 7.78/1.48      ( k1_orders_2(sK4,k2_struct_0(sK4)) != X0
% 7.78/1.48      | k1_xboole_0 != X0
% 7.78/1.48      | k1_xboole_0 = k1_orders_2(sK4,k2_struct_0(sK4)) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1079]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_10269,plain,
% 7.78/1.48      ( k1_orders_2(sK4,k2_struct_0(sK4)) != k1_xboole_0
% 7.78/1.48      | k1_xboole_0 = k1_orders_2(sK4,k2_struct_0(sK4))
% 7.78/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1704]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_11951,plain,
% 7.78/1.48      ( sK3(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),sK4,k2_struct_0(sK4)) = sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_11883,c_19,c_5764,c_10269]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_16,plain,
% 7.78/1.48      ( r2_orders_2(X0,X1,sK3(X2,X0,X3))
% 7.78/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.78/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 7.78/1.48      | ~ r2_hidden(X1,X3)
% 7.78/1.48      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 7.78/1.48      | v2_struct_0(X0)
% 7.78/1.48      | ~ v3_orders_2(X0)
% 7.78/1.48      | ~ v4_orders_2(X0)
% 7.78/1.48      | ~ v5_orders_2(X0)
% 7.78/1.48      | ~ l1_orders_2(X0) ),
% 7.78/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_514,plain,
% 7.78/1.48      ( r2_orders_2(X0,X1,sK3(X2,X0,X3))
% 7.78/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.78/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 7.78/1.48      | ~ r2_hidden(X1,X3)
% 7.78/1.48      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 7.78/1.48      | v2_struct_0(X0)
% 7.78/1.48      | ~ v3_orders_2(X0)
% 7.78/1.48      | ~ v4_orders_2(X0)
% 7.78/1.48      | ~ l1_orders_2(X0)
% 7.78/1.48      | sK4 != X0 ),
% 7.78/1.48      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_515,plain,
% 7.78/1.48      ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
% 7.78/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.78/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | ~ r2_hidden(X0,X2)
% 7.78/1.48      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2))
% 7.78/1.48      | v2_struct_0(sK4)
% 7.78/1.48      | ~ v3_orders_2(sK4)
% 7.78/1.48      | ~ v4_orders_2(sK4)
% 7.78/1.48      | ~ l1_orders_2(sK4) ),
% 7.78/1.48      inference(unflattening,[status(thm)],[c_514]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_519,plain,
% 7.78/1.48      ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
% 7.78/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.78/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | ~ r2_hidden(X0,X2)
% 7.78/1.48      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2)) ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_515,c_24,c_23,c_22,c_20]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1514,plain,
% 7.78/1.48      ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2)) = iProver_top
% 7.78/1.48      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 7.78/1.48      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.78/1.48      | r2_hidden(X0,X2) != iProver_top
% 7.78/1.48      | r2_hidden(X1,a_2_0_orders_2(sK4,X2)) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1607,plain,
% 7.78/1.48      ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2)) = iProver_top
% 7.78/1.48      | m1_subset_1(X0,k2_struct_0(sK4)) != iProver_top
% 7.78/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 7.78/1.48      | r2_hidden(X0,X2) != iProver_top
% 7.78/1.48      | r2_hidden(X1,a_2_0_orders_2(sK4,X2)) != iProver_top ),
% 7.78/1.48      inference(light_normalisation,[status(thm)],[c_1514,c_727]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_8,plain,
% 7.78/1.48      ( ~ r2_orders_2(X0,X1,X1)
% 7.78/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.78/1.48      | ~ l1_orders_2(X0) ),
% 7.78/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_731,plain,
% 7.78/1.48      ( ~ r2_orders_2(X0,X1,X1)
% 7.78/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.78/1.48      | sK4 != X0 ),
% 7.78/1.48      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_732,plain,
% 7.78/1.48      ( ~ r2_orders_2(sK4,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 7.78/1.48      inference(unflattening,[status(thm)],[c_731]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1506,plain,
% 7.78/1.48      ( r2_orders_2(sK4,X0,X0) != iProver_top
% 7.78/1.48      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1545,plain,
% 7.78/1.48      ( r2_orders_2(sK4,X0,X0) != iProver_top
% 7.78/1.48      | m1_subset_1(X0,k2_struct_0(sK4)) != iProver_top ),
% 7.78/1.48      inference(light_normalisation,[status(thm)],[c_1506,c_727]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2110,plain,
% 7.78/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 7.78/1.48      | m1_subset_1(sK3(X1,sK4,X0),k2_struct_0(sK4)) != iProver_top
% 7.78/1.48      | r2_hidden(X1,a_2_0_orders_2(sK4,X0)) != iProver_top
% 7.78/1.48      | r2_hidden(sK3(X1,sK4,X0),X0) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_1607,c_1545]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_18,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.48      | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
% 7.78/1.48      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 7.78/1.48      | v2_struct_0(X1)
% 7.78/1.48      | ~ v3_orders_2(X1)
% 7.78/1.48      | ~ v4_orders_2(X1)
% 7.78/1.48      | ~ v5_orders_2(X1)
% 7.78/1.48      | ~ l1_orders_2(X1) ),
% 7.78/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_565,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.48      | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
% 7.78/1.48      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 7.78/1.48      | v2_struct_0(X1)
% 7.78/1.48      | ~ v3_orders_2(X1)
% 7.78/1.48      | ~ v4_orders_2(X1)
% 7.78/1.48      | ~ l1_orders_2(X1)
% 7.78/1.48      | sK4 != X1 ),
% 7.78/1.48      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_566,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
% 7.78/1.48      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 7.78/1.48      | v2_struct_0(sK4)
% 7.78/1.48      | ~ v3_orders_2(sK4)
% 7.78/1.48      | ~ v4_orders_2(sK4)
% 7.78/1.48      | ~ l1_orders_2(sK4) ),
% 7.78/1.48      inference(unflattening,[status(thm)],[c_565]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_570,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
% 7.78/1.48      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0)) ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_566,c_24,c_23,c_22,c_20]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1512,plain,
% 7.78/1.48      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.78/1.48      | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4)) = iProver_top
% 7.78/1.48      | r2_hidden(X1,a_2_0_orders_2(sK4,X0)) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_570]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1573,plain,
% 7.78/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 7.78/1.48      | m1_subset_1(sK3(X1,sK4,X0),k2_struct_0(sK4)) = iProver_top
% 7.78/1.48      | r2_hidden(X1,a_2_0_orders_2(sK4,X0)) != iProver_top ),
% 7.78/1.48      inference(light_normalisation,[status(thm)],[c_1512,c_727]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_3131,plain,
% 7.78/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 7.78/1.48      | r2_hidden(X1,a_2_0_orders_2(sK4,X0)) != iProver_top
% 7.78/1.48      | r2_hidden(sK3(X1,sK4,X0),X0) != iProver_top ),
% 7.78/1.48      inference(global_propositional_subsumption,[status(thm)],[c_2110,c_1573]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_11958,plain,
% 7.78/1.48      ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 7.78/1.48      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,k2_struct_0(sK4))) != iProver_top
% 7.78/1.48      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_11951,c_3131]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_11984,plain,
% 7.78/1.48      ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top
% 7.78/1.48      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) != iProver_top
% 7.78/1.48      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) != iProver_top ),
% 7.78/1.48      inference(light_normalisation,[status(thm)],[c_11958,c_2695]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_17434,plain,
% 7.78/1.48      ( m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.78/1.48      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_660]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_17451,plain,
% 7.78/1.48      ( m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 7.78/1.48      | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_17434]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_18086,plain,
% 7.78/1.48      ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_15478,c_20,c_19,c_49,c_67,c_1093,c_1101,c_1702,c_1855,
% 7.78/1.48                 c_2361,c_2459,c_2461,c_3606,c_4393,c_6393,c_11984,c_17451]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_18091,plain,
% 7.78/1.48      ( r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4)) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_1516,c_18086]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_18221,plain,
% 7.78/1.48      ( $false ),
% 7.78/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_18091,c_2101]) ).
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  ------                               Statistics
% 7.78/1.48  
% 7.78/1.48  ------ Selected
% 7.78/1.48  
% 7.78/1.48  total_time:                             0.661
% 7.78/1.48  
%------------------------------------------------------------------------------
