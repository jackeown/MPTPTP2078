%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:09 EST 2020

% Result     : Theorem 19.85s
% Output     : CNFRefutation 19.85s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 299 expanded)
%              Number of clauses        :   90 ( 122 expanded)
%              Number of leaves         :   21 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  617 (1225 expanded)
%              Number of equality atoms :   88 ( 173 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK4(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
        & r2_hidden(sK3(X1,X2,X3),X2)
        & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
                & r2_hidden(sK3(X1,X2,X3),X2)
                & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK4(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f45,f47,f46])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | r2_hidden(sK3(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_orders_2(X1,X2))
      | r2_hidden(sK3(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f75])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f41])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f32,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( u1_struct_0(sK5) != k2_orders_2(sK5,k1_struct_0(sK5))
      & l1_orders_2(sK5)
      & v5_orders_2(sK5)
      & v4_orders_2(sK5)
      & v3_orders_2(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( u1_struct_0(sK5) != k2_orders_2(sK5,k1_struct_0(sK5))
    & l1_orders_2(sK5)
    & v5_orders_2(sK5)
    & v4_orders_2(sK5)
    & v3_orders_2(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f49])).

fof(f82,plain,(
    u1_struct_0(sK5) != k2_orders_2(sK5,k1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f50])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | m1_subset_1(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2407,plain,
    ( ~ r2_hidden(sK2(X0,X1),X2)
    | r2_hidden(sK2(X0,X1),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_25406,plain,
    ( ~ r2_hidden(sK2(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),X0)
    | r2_hidden(sK2(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),k2_orders_2(sK5,k1_struct_0(sK5)))
    | ~ r1_tarski(X0,k2_orders_2(sK5,k1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_2407])).

cnf(c_71177,plain,
    ( r2_hidden(sK2(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),k2_orders_2(sK5,k1_struct_0(sK5)))
    | ~ r2_hidden(sK2(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
    | ~ r1_tarski(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_25406])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2252,plain,
    ( ~ r2_hidden(X0,k1_struct_0(X1))
    | ~ v1_xboole_0(k1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_57613,plain,
    ( ~ r2_hidden(sK3(sK5,k1_struct_0(X0),sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5)))),k1_struct_0(X0))
    | ~ v1_xboole_0(k1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2252])).

cnf(c_57619,plain,
    ( ~ r2_hidden(sK3(sK5,k1_struct_0(sK5),sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5)))),k1_struct_0(sK5))
    | ~ v1_xboole_0(k1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_57613])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_10273,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
    | r2_hidden(sK3(sK5,X0,sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5)))),X0)
    | r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),a_2_1_orders_2(sK5,X0))
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_57610,plain,
    ( ~ m1_subset_1(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
    | ~ m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK3(sK5,k1_struct_0(X0),sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5)))),k1_struct_0(X0))
    | r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),a_2_1_orders_2(sK5,k1_struct_0(X0)))
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(instantiation,[status(thm)],[c_10273])).

cnf(c_57615,plain,
    ( ~ m1_subset_1(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
    | ~ m1_subset_1(k1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK3(sK5,k1_struct_0(sK5),sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5)))),k1_struct_0(sK5))
    | r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),a_2_1_orders_2(sK5,k1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(instantiation,[status(thm)],[c_57610])).

cnf(c_372,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2830,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),k2_orders_2(sK5,k1_struct_0(sK5)))
    | k2_orders_2(sK5,k1_struct_0(sK5)) != X1
    | sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) != X0 ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_4733,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),X0)
    | r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),k2_orders_2(sK5,k1_struct_0(sK5)))
    | k2_orders_2(sK5,k1_struct_0(sK5)) != X0
    | sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) != sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_2830])).

cnf(c_12711,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),a_2_1_orders_2(X0,X1))
    | r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),k2_orders_2(sK5,k1_struct_0(sK5)))
    | k2_orders_2(sK5,k1_struct_0(sK5)) != a_2_1_orders_2(X0,X1)
    | sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) != sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_4733])).

cnf(c_51638,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),a_2_1_orders_2(sK5,k1_struct_0(sK5)))
    | r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),k2_orders_2(sK5,k1_struct_0(sK5)))
    | k2_orders_2(sK5,k1_struct_0(sK5)) != a_2_1_orders_2(sK5,k1_struct_0(sK5))
    | sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) != sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_12711])).

cnf(c_371,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2625,plain,
    ( X0 != X1
    | k2_orders_2(sK5,k1_struct_0(sK5)) != X1
    | k2_orders_2(sK5,k1_struct_0(sK5)) = X0 ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_12136,plain,
    ( X0 != k2_orders_2(sK5,k1_struct_0(sK5))
    | k2_orders_2(sK5,k1_struct_0(sK5)) = X0
    | k2_orders_2(sK5,k1_struct_0(sK5)) != k2_orders_2(sK5,k1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2625])).

cnf(c_28933,plain,
    ( a_2_1_orders_2(sK5,k1_struct_0(sK5)) != k2_orders_2(sK5,k1_struct_0(sK5))
    | k2_orders_2(sK5,k1_struct_0(sK5)) = a_2_1_orders_2(sK5,k1_struct_0(sK5))
    | k2_orders_2(sK5,k1_struct_0(sK5)) != k2_orders_2(sK5,k1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_12136])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK2(X1,X0),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_214,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_213])).

cnf(c_276,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_214])).

cnf(c_20456,plain,
    ( ~ r2_hidden(sK2(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),k2_orders_2(sK5,k1_struct_0(sK5)))
    | ~ r1_tarski(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5))
    | k2_orders_2(sK5,k1_struct_0(sK5)) = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_20448,plain,
    ( ~ r2_hidden(sK2(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)),u1_struct_0(sK5))
    | ~ r1_tarski(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5)))
    | u1_struct_0(sK5) = k2_orders_2(sK5,k1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3729,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_13118,plain,
    ( ~ m1_subset_1(sK2(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
    | r2_hidden(sK2(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3729])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3153,plain,
    ( ~ m1_subset_1(k2_orders_2(sK5,k1_struct_0(sK5)),k1_zfmisc_1(X0))
    | r1_tarski(k2_orders_2(sK5,k1_struct_0(sK5)),X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_8926,plain,
    ( ~ m1_subset_1(k2_orders_2(sK5,k1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3153])).

cnf(c_3734,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,u1_struct_0(X2))
    | ~ r1_tarski(X1,u1_struct_0(X2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7700,plain,
    ( ~ r2_hidden(sK2(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)),k2_orders_2(sK5,k1_struct_0(sK5)))
    | r2_hidden(sK2(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)),u1_struct_0(X0))
    | ~ r1_tarski(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_3734])).

cnf(c_7702,plain,
    ( ~ r2_hidden(sK2(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)),k2_orders_2(sK5,k1_struct_0(sK5)))
    | r2_hidden(sK2(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)),u1_struct_0(sK5))
    | ~ r1_tarski(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_7700])).

cnf(c_370,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3635,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_371,c_370])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3856,plain,
    ( ~ v1_xboole_0(X0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3635,c_4])).

cnf(c_3884,plain,
    ( ~ v1_xboole_0(X0)
    | X0 = X1
    | X1 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3856,c_371])).

cnf(c_5789,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(resolution,[status(thm)],[c_3884,c_3856])).

cnf(c_26,negated_conjecture,
    ( u1_struct_0(sK5) != k2_orders_2(sK5,k1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_5804,plain,
    ( ~ v1_xboole_0(k2_orders_2(sK5,k1_struct_0(sK5)))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_5789,c_26])).

cnf(c_4734,plain,
    ( sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) = sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_3794,plain,
    ( ~ r2_hidden(sK0(k1_struct_0(X0),u1_struct_0(X1)),k1_struct_0(X0))
    | ~ v1_xboole_0(k1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2252])).

cnf(c_3800,plain,
    ( ~ r2_hidden(sK0(k1_struct_0(sK5),u1_struct_0(sK5)),k1_struct_0(sK5))
    | ~ v1_xboole_0(k1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3794])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1703,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(X1)),X0)
    | r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3793,plain,
    ( r2_hidden(sK0(k1_struct_0(X0),u1_struct_0(X1)),k1_struct_0(X0))
    | r1_tarski(k1_struct_0(X0),u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_1703])).

cnf(c_3796,plain,
    ( r2_hidden(sK0(k1_struct_0(sK5),u1_struct_0(sK5)),k1_struct_0(sK5))
    | r1_tarski(k1_struct_0(sK5),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3793])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_313,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_5])).

cnf(c_314,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_313])).

cnf(c_2344,plain,
    ( m1_subset_1(X0,u1_struct_0(X1))
    | ~ r2_hidden(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_3745,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
    | ~ r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2344])).

cnf(c_3036,plain,
    ( k2_orders_2(sK5,k1_struct_0(sK5)) = k2_orders_2(sK5,k1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2368,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),k2_orders_2(sK5,k1_struct_0(sK5)))
    | r1_tarski(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1557,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2084,plain,
    ( m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_struct_0(X0),u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_1557])).

cnf(c_2086,plain,
    ( m1_subset_1(k1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(k1_struct_0(sK5),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2084])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK2(X1,X0),X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_277,plain,
    ( m1_subset_1(sK2(X0,X1),X0)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_214])).

cnf(c_1853,plain,
    ( m1_subset_1(sK2(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
    | ~ r1_tarski(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5))
    | k2_orders_2(sK5,k1_struct_0(sK5)) = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_1846,plain,
    ( r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
    | r1_tarski(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1688,plain,
    ( ~ m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,k1_struct_0(X0)) = k2_orders_2(X1,k1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1699,plain,
    ( ~ m1_subset_1(k1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | ~ l1_orders_2(sK5)
    | a_2_1_orders_2(sK5,k1_struct_0(sK5)) = k2_orders_2(sK5,k1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1688])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1689,plain,
    ( m1_subset_1(k2_orders_2(X0,k1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1695,plain,
    ( m1_subset_1(k2_orders_2(sK5,k1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(k1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v5_orders_2(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(instantiation,[status(thm)],[c_1689])).

cnf(c_1470,plain,
    ( k2_orders_2(sK5,k1_struct_0(sK5)) != X0
    | u1_struct_0(sK5) != X0
    | u1_struct_0(sK5) = k2_orders_2(sK5,k1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_1639,plain,
    ( k2_orders_2(sK5,k1_struct_0(sK5)) != u1_struct_0(sK5)
    | u1_struct_0(sK5) = k2_orders_2(sK5,k1_struct_0(sK5))
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_1623,plain,
    ( ~ m1_subset_1(sK2(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)),k2_orders_2(sK5,k1_struct_0(sK5)))
    | r2_hidden(sK2(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)),k2_orders_2(sK5,k1_struct_0(sK5)))
    | v1_xboole_0(k2_orders_2(sK5,k1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1620,plain,
    ( m1_subset_1(sK2(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)),k2_orders_2(sK5,k1_struct_0(sK5)))
    | ~ r1_tarski(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5)))
    | u1_struct_0(sK5) = k2_orders_2(sK5,k1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_399,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_378,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_391,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_378])).

cnf(c_16,plain,
    ( ~ l1_struct_0(X0)
    | v1_xboole_0(k1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_65,plain,
    ( ~ l1_struct_0(sK5)
    | v1_xboole_0(k1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_19,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_56,plain,
    ( ~ l1_orders_2(sK5)
    | l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_27,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_28,negated_conjecture,
    ( v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_29,negated_conjecture,
    ( v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,negated_conjecture,
    ( v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_71177,c_57619,c_57615,c_51638,c_28933,c_20456,c_20448,c_13118,c_8926,c_7702,c_5804,c_4734,c_3800,c_3796,c_3745,c_3036,c_2368,c_2086,c_1853,c_1846,c_1699,c_1695,c_1639,c_1623,c_1620,c_399,c_391,c_65,c_56,c_26,c_27,c_28,c_29,c_30,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.85/2.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.85/2.98  
% 19.85/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.85/2.98  
% 19.85/2.98  ------  iProver source info
% 19.85/2.98  
% 19.85/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.85/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.85/2.98  git: non_committed_changes: false
% 19.85/2.98  git: last_make_outside_of_git: false
% 19.85/2.98  
% 19.85/2.98  ------ 
% 19.85/2.98  ------ Parsing...
% 19.85/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.85/2.98  
% 19.85/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.85/2.98  
% 19.85/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.85/2.98  
% 19.85/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.85/2.98  ------ Proving...
% 19.85/2.98  ------ Problem Properties 
% 19.85/2.98  
% 19.85/2.98  
% 19.85/2.98  clauses                                 32
% 19.85/2.98  conjectures                             6
% 19.85/2.98  EPR                                     14
% 19.85/2.98  Horn                                    21
% 19.85/2.98  unary                                   8
% 19.85/2.98  binary                                  10
% 19.85/2.98  lits                                    113
% 19.85/2.98  lits eq                                 7
% 19.85/2.98  fd_pure                                 0
% 19.85/2.98  fd_pseudo                               0
% 19.85/2.98  fd_cond                                 1
% 19.85/2.98  fd_pseudo_cond                          2
% 19.85/2.98  AC symbols                              0
% 19.85/2.98  
% 19.85/2.98  ------ Input Options Time Limit: Unbounded
% 19.85/2.98  
% 19.85/2.98  
% 19.85/2.98  ------ 
% 19.85/2.98  Current options:
% 19.85/2.98  ------ 
% 19.85/2.98  
% 19.85/2.98  
% 19.85/2.98  
% 19.85/2.98  
% 19.85/2.98  ------ Proving...
% 19.85/2.98  
% 19.85/2.98  
% 19.85/2.98  % SZS status Theorem for theBenchmark.p
% 19.85/2.98  
% 19.85/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.85/2.98  
% 19.85/2.98  fof(f1,axiom,(
% 19.85/2.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.85/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.98  
% 19.85/2.98  fof(f17,plain,(
% 19.85/2.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 19.85/2.98    inference(ennf_transformation,[],[f1])).
% 19.85/2.98  
% 19.85/2.98  fof(f34,plain,(
% 19.85/2.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 19.85/2.98    inference(nnf_transformation,[],[f17])).
% 19.85/2.98  
% 19.85/2.98  fof(f35,plain,(
% 19.85/2.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.85/2.98    inference(rectify,[],[f34])).
% 19.85/2.98  
% 19.85/2.98  fof(f36,plain,(
% 19.85/2.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.85/2.98    introduced(choice_axiom,[])).
% 19.85/2.98  
% 19.85/2.98  fof(f37,plain,(
% 19.85/2.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.85/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 19.85/2.98  
% 19.85/2.98  fof(f51,plain,(
% 19.85/2.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 19.85/2.98    inference(cnf_transformation,[],[f37])).
% 19.85/2.98  
% 19.85/2.98  fof(f4,axiom,(
% 19.85/2.98    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 19.85/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.98  
% 19.85/2.98  fof(f19,plain,(
% 19.85/2.98    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 19.85/2.98    inference(ennf_transformation,[],[f4])).
% 19.85/2.98  
% 19.85/2.98  fof(f56,plain,(
% 19.85/2.98    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 19.85/2.98    inference(cnf_transformation,[],[f19])).
% 19.85/2.98  
% 19.85/2.98  fof(f14,axiom,(
% 19.85/2.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 19.85/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.98  
% 19.85/2.98  fof(f30,plain,(
% 19.85/2.98    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 19.85/2.98    inference(ennf_transformation,[],[f14])).
% 19.85/2.98  
% 19.85/2.98  fof(f31,plain,(
% 19.85/2.98    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 19.85/2.98    inference(flattening,[],[f30])).
% 19.85/2.98  
% 19.85/2.98  fof(f44,plain,(
% 19.85/2.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 19.85/2.98    inference(nnf_transformation,[],[f31])).
% 19.85/2.98  
% 19.85/2.98  fof(f45,plain,(
% 19.85/2.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 19.85/2.98    inference(rectify,[],[f44])).
% 19.85/2.98  
% 19.85/2.98  fof(f47,plain,(
% 19.85/2.98    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK4(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 19.85/2.98    introduced(choice_axiom,[])).
% 19.85/2.98  
% 19.85/2.98  fof(f46,plain,(
% 19.85/2.98    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK3(X1,X2,X3)) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))))),
% 19.85/2.98    introduced(choice_axiom,[])).
% 19.85/2.98  
% 19.85/2.98  fof(f48,plain,(
% 19.85/2.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK3(X1,X2,X3)) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK4(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 19.85/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f45,f47,f46])).
% 19.85/2.98  
% 19.85/2.98  fof(f75,plain,(
% 19.85/2.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | r2_hidden(sK3(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 19.85/2.98    inference(cnf_transformation,[],[f48])).
% 19.85/2.98  
% 19.85/2.98  fof(f84,plain,(
% 19.85/2.98    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_orders_2(X1,X2)) | r2_hidden(sK3(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 19.85/2.98    inference(equality_resolution,[],[f75])).
% 19.85/2.98  
% 19.85/2.98  fof(f7,axiom,(
% 19.85/2.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 19.85/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.98  
% 19.85/2.98  fof(f21,plain,(
% 19.85/2.98    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.85/2.98    inference(ennf_transformation,[],[f7])).
% 19.85/2.98  
% 19.85/2.98  fof(f22,plain,(
% 19.85/2.98    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.85/2.98    inference(flattening,[],[f21])).
% 19.85/2.98  
% 19.85/2.98  fof(f41,plain,(
% 19.85/2.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),X0)))),
% 19.85/2.98    introduced(choice_axiom,[])).
% 19.85/2.98  
% 19.85/2.98  fof(f42,plain,(
% 19.85/2.98    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.85/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f41])).
% 19.85/2.98  
% 19.85/2.98  fof(f63,plain,(
% 19.85/2.98    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.85/2.98    inference(cnf_transformation,[],[f42])).
% 19.85/2.98  
% 19.85/2.98  fof(f8,axiom,(
% 19.85/2.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.85/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.98  
% 19.85/2.98  fof(f43,plain,(
% 19.85/2.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.85/2.98    inference(nnf_transformation,[],[f8])).
% 19.85/2.98  
% 19.85/2.98  fof(f65,plain,(
% 19.85/2.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.85/2.98    inference(cnf_transformation,[],[f43])).
% 19.85/2.98  
% 19.85/2.98  fof(f5,axiom,(
% 19.85/2.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 19.85/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.98  
% 19.85/2.98  fof(f20,plain,(
% 19.85/2.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 19.85/2.98    inference(ennf_transformation,[],[f5])).
% 19.85/2.98  
% 19.85/2.98  fof(f38,plain,(
% 19.85/2.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 19.85/2.98    inference(nnf_transformation,[],[f20])).
% 19.85/2.98  
% 19.85/2.98  fof(f57,plain,(
% 19.85/2.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 19.85/2.98    inference(cnf_transformation,[],[f38])).
% 19.85/2.98  
% 19.85/2.98  fof(f64,plain,(
% 19.85/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.85/2.98    inference(cnf_transformation,[],[f43])).
% 19.85/2.98  
% 19.85/2.98  fof(f3,axiom,(
% 19.85/2.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 19.85/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.98  
% 19.85/2.98  fof(f18,plain,(
% 19.85/2.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 19.85/2.98    inference(ennf_transformation,[],[f3])).
% 19.85/2.98  
% 19.85/2.98  fof(f55,plain,(
% 19.85/2.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 19.85/2.98    inference(cnf_transformation,[],[f18])).
% 19.85/2.98  
% 19.85/2.98  fof(f15,conjecture,(
% 19.85/2.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 19.85/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.98  
% 19.85/2.98  fof(f16,negated_conjecture,(
% 19.85/2.98    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 19.85/2.98    inference(negated_conjecture,[],[f15])).
% 19.85/2.98  
% 19.85/2.98  fof(f32,plain,(
% 19.85/2.98    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 19.85/2.98    inference(ennf_transformation,[],[f16])).
% 19.85/2.98  
% 19.85/2.98  fof(f33,plain,(
% 19.85/2.98    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 19.85/2.98    inference(flattening,[],[f32])).
% 19.85/2.98  
% 19.85/2.98  fof(f49,plain,(
% 19.85/2.98    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (u1_struct_0(sK5) != k2_orders_2(sK5,k1_struct_0(sK5)) & l1_orders_2(sK5) & v5_orders_2(sK5) & v4_orders_2(sK5) & v3_orders_2(sK5) & ~v2_struct_0(sK5))),
% 19.85/2.98    introduced(choice_axiom,[])).
% 19.85/2.98  
% 19.85/2.98  fof(f50,plain,(
% 19.85/2.98    u1_struct_0(sK5) != k2_orders_2(sK5,k1_struct_0(sK5)) & l1_orders_2(sK5) & v5_orders_2(sK5) & v4_orders_2(sK5) & v3_orders_2(sK5) & ~v2_struct_0(sK5)),
% 19.85/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f49])).
% 19.85/2.98  
% 19.85/2.98  fof(f82,plain,(
% 19.85/2.98    u1_struct_0(sK5) != k2_orders_2(sK5,k1_struct_0(sK5))),
% 19.85/2.98    inference(cnf_transformation,[],[f50])).
% 19.85/2.98  
% 19.85/2.98  fof(f52,plain,(
% 19.85/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 19.85/2.98    inference(cnf_transformation,[],[f37])).
% 19.85/2.98  
% 19.85/2.98  fof(f58,plain,(
% 19.85/2.98    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 19.85/2.98    inference(cnf_transformation,[],[f38])).
% 19.85/2.98  
% 19.85/2.98  fof(f53,plain,(
% 19.85/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 19.85/2.98    inference(cnf_transformation,[],[f37])).
% 19.85/2.98  
% 19.85/2.98  fof(f62,plain,(
% 19.85/2.98    ( ! [X0,X1] : (X0 = X1 | m1_subset_1(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.85/2.98    inference(cnf_transformation,[],[f42])).
% 19.85/2.98  
% 19.85/2.98  fof(f11,axiom,(
% 19.85/2.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 19.85/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.98  
% 19.85/2.98  fof(f25,plain,(
% 19.85/2.98    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 19.85/2.98    inference(ennf_transformation,[],[f11])).
% 19.85/2.98  
% 19.85/2.98  fof(f26,plain,(
% 19.85/2.98    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 19.85/2.98    inference(flattening,[],[f25])).
% 19.85/2.98  
% 19.85/2.98  fof(f68,plain,(
% 19.85/2.98    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 19.85/2.98    inference(cnf_transformation,[],[f26])).
% 19.85/2.98  
% 19.85/2.98  fof(f12,axiom,(
% 19.85/2.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 19.85/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.98  
% 19.85/2.98  fof(f27,plain,(
% 19.85/2.98    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 19.85/2.98    inference(ennf_transformation,[],[f12])).
% 19.85/2.98  
% 19.85/2.98  fof(f28,plain,(
% 19.85/2.98    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 19.85/2.98    inference(flattening,[],[f27])).
% 19.85/2.98  
% 19.85/2.98  fof(f69,plain,(
% 19.85/2.98    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 19.85/2.98    inference(cnf_transformation,[],[f28])).
% 19.85/2.98  
% 19.85/2.98  fof(f10,axiom,(
% 19.85/2.98    ! [X0] : (l1_struct_0(X0) => v1_xboole_0(k1_struct_0(X0)))),
% 19.85/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.98  
% 19.85/2.98  fof(f24,plain,(
% 19.85/2.98    ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0))),
% 19.85/2.98    inference(ennf_transformation,[],[f10])).
% 19.85/2.98  
% 19.85/2.98  fof(f67,plain,(
% 19.85/2.98    ( ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 19.85/2.98    inference(cnf_transformation,[],[f24])).
% 19.85/2.98  
% 19.85/2.98  fof(f13,axiom,(
% 19.85/2.98    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 19.85/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.98  
% 19.85/2.98  fof(f29,plain,(
% 19.85/2.98    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 19.85/2.98    inference(ennf_transformation,[],[f13])).
% 19.85/2.98  
% 19.85/2.98  fof(f70,plain,(
% 19.85/2.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 19.85/2.98    inference(cnf_transformation,[],[f29])).
% 19.85/2.98  
% 19.85/2.98  fof(f81,plain,(
% 19.85/2.98    l1_orders_2(sK5)),
% 19.85/2.98    inference(cnf_transformation,[],[f50])).
% 19.85/2.98  
% 19.85/2.98  fof(f80,plain,(
% 19.85/2.98    v5_orders_2(sK5)),
% 19.85/2.98    inference(cnf_transformation,[],[f50])).
% 19.85/2.98  
% 19.85/2.98  fof(f79,plain,(
% 19.85/2.98    v4_orders_2(sK5)),
% 19.85/2.98    inference(cnf_transformation,[],[f50])).
% 19.85/2.98  
% 19.85/2.98  fof(f78,plain,(
% 19.85/2.98    v3_orders_2(sK5)),
% 19.85/2.98    inference(cnf_transformation,[],[f50])).
% 19.85/2.98  
% 19.85/2.98  fof(f77,plain,(
% 19.85/2.98    ~v2_struct_0(sK5)),
% 19.85/2.98    inference(cnf_transformation,[],[f50])).
% 19.85/2.98  
% 19.85/2.98  cnf(c_2,plain,
% 19.85/2.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 19.85/2.98      inference(cnf_transformation,[],[f51]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_2407,plain,
% 19.85/2.98      ( ~ r2_hidden(sK2(X0,X1),X2)
% 19.85/2.98      | r2_hidden(sK2(X0,X1),X1)
% 19.85/2.98      | ~ r1_tarski(X2,X1) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_2]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_25406,plain,
% 19.85/2.98      ( ~ r2_hidden(sK2(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),X0)
% 19.85/2.98      | r2_hidden(sK2(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),k2_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | ~ r1_tarski(X0,k2_orders_2(sK5,k1_struct_0(sK5))) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_2407]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_71177,plain,
% 19.85/2.98      ( r2_hidden(sK2(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),k2_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | ~ r2_hidden(sK2(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
% 19.85/2.98      | ~ r1_tarski(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_25406]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_5,plain,
% 19.85/2.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 19.85/2.98      inference(cnf_transformation,[],[f56]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_2252,plain,
% 19.85/2.98      ( ~ r2_hidden(X0,k1_struct_0(X1))
% 19.85/2.98      | ~ v1_xboole_0(k1_struct_0(X1)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_5]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_57613,plain,
% 19.85/2.98      ( ~ r2_hidden(sK3(sK5,k1_struct_0(X0),sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5)))),k1_struct_0(X0))
% 19.85/2.98      | ~ v1_xboole_0(k1_struct_0(X0)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_2252]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_57619,plain,
% 19.85/2.98      ( ~ r2_hidden(sK3(sK5,k1_struct_0(sK5),sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5)))),k1_struct_0(sK5))
% 19.85/2.98      | ~ v1_xboole_0(k1_struct_0(sK5)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_57613]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_21,plain,
% 19.85/2.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 19.85/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.98      | r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 19.85/2.98      | r2_hidden(sK3(X1,X2,X0),X2)
% 19.85/2.98      | v2_struct_0(X1)
% 19.85/2.98      | ~ v3_orders_2(X1)
% 19.85/2.98      | ~ v4_orders_2(X1)
% 19.85/2.98      | ~ v5_orders_2(X1)
% 19.85/2.98      | ~ l1_orders_2(X1) ),
% 19.85/2.98      inference(cnf_transformation,[],[f84]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_10273,plain,
% 19.85/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.85/2.98      | ~ m1_subset_1(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
% 19.85/2.98      | r2_hidden(sK3(sK5,X0,sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5)))),X0)
% 19.85/2.98      | r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),a_2_1_orders_2(sK5,X0))
% 19.85/2.98      | v2_struct_0(sK5)
% 19.85/2.98      | ~ v3_orders_2(sK5)
% 19.85/2.98      | ~ v4_orders_2(sK5)
% 19.85/2.98      | ~ v5_orders_2(sK5)
% 19.85/2.98      | ~ l1_orders_2(sK5) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_21]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_57610,plain,
% 19.85/2.98      ( ~ m1_subset_1(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
% 19.85/2.98      | ~ m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 19.85/2.98      | r2_hidden(sK3(sK5,k1_struct_0(X0),sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5)))),k1_struct_0(X0))
% 19.85/2.98      | r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),a_2_1_orders_2(sK5,k1_struct_0(X0)))
% 19.85/2.98      | v2_struct_0(sK5)
% 19.85/2.98      | ~ v3_orders_2(sK5)
% 19.85/2.98      | ~ v4_orders_2(sK5)
% 19.85/2.98      | ~ v5_orders_2(sK5)
% 19.85/2.98      | ~ l1_orders_2(sK5) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_10273]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_57615,plain,
% 19.85/2.98      ( ~ m1_subset_1(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
% 19.85/2.98      | ~ m1_subset_1(k1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 19.85/2.98      | r2_hidden(sK3(sK5,k1_struct_0(sK5),sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5)))),k1_struct_0(sK5))
% 19.85/2.98      | r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),a_2_1_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | v2_struct_0(sK5)
% 19.85/2.98      | ~ v3_orders_2(sK5)
% 19.85/2.98      | ~ v4_orders_2(sK5)
% 19.85/2.98      | ~ v5_orders_2(sK5)
% 19.85/2.98      | ~ l1_orders_2(sK5) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_57610]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_372,plain,
% 19.85/2.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.85/2.98      theory(equality) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_2830,plain,
% 19.85/2.98      ( ~ r2_hidden(X0,X1)
% 19.85/2.98      | r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),k2_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | k2_orders_2(sK5,k1_struct_0(sK5)) != X1
% 19.85/2.98      | sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) != X0 ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_372]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_4733,plain,
% 19.85/2.98      ( ~ r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),X0)
% 19.85/2.98      | r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),k2_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | k2_orders_2(sK5,k1_struct_0(sK5)) != X0
% 19.85/2.98      | sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) != sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_2830]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_12711,plain,
% 19.85/2.98      ( ~ r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),a_2_1_orders_2(X0,X1))
% 19.85/2.98      | r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),k2_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | k2_orders_2(sK5,k1_struct_0(sK5)) != a_2_1_orders_2(X0,X1)
% 19.85/2.98      | sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) != sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_4733]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_51638,plain,
% 19.85/2.98      ( ~ r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),a_2_1_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),k2_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | k2_orders_2(sK5,k1_struct_0(sK5)) != a_2_1_orders_2(sK5,k1_struct_0(sK5))
% 19.85/2.98      | sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) != sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_12711]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_371,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_2625,plain,
% 19.85/2.98      ( X0 != X1
% 19.85/2.98      | k2_orders_2(sK5,k1_struct_0(sK5)) != X1
% 19.85/2.98      | k2_orders_2(sK5,k1_struct_0(sK5)) = X0 ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_371]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_12136,plain,
% 19.85/2.98      ( X0 != k2_orders_2(sK5,k1_struct_0(sK5))
% 19.85/2.98      | k2_orders_2(sK5,k1_struct_0(sK5)) = X0
% 19.85/2.98      | k2_orders_2(sK5,k1_struct_0(sK5)) != k2_orders_2(sK5,k1_struct_0(sK5)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_2625]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_28933,plain,
% 19.85/2.98      ( a_2_1_orders_2(sK5,k1_struct_0(sK5)) != k2_orders_2(sK5,k1_struct_0(sK5))
% 19.85/2.98      | k2_orders_2(sK5,k1_struct_0(sK5)) = a_2_1_orders_2(sK5,k1_struct_0(sK5))
% 19.85/2.98      | k2_orders_2(sK5,k1_struct_0(sK5)) != k2_orders_2(sK5,k1_struct_0(sK5)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_12136]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_11,plain,
% 19.85/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.85/2.98      | ~ r2_hidden(sK2(X1,X0),X0)
% 19.85/2.98      | X0 = X1 ),
% 19.85/2.98      inference(cnf_transformation,[],[f63]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_13,plain,
% 19.85/2.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.85/2.98      inference(cnf_transformation,[],[f65]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_213,plain,
% 19.85/2.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.85/2.98      inference(prop_impl,[status(thm)],[c_13]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_214,plain,
% 19.85/2.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.85/2.98      inference(renaming,[status(thm)],[c_213]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_276,plain,
% 19.85/2.98      ( ~ r2_hidden(sK2(X0,X1),X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 19.85/2.98      inference(bin_hyper_res,[status(thm)],[c_11,c_214]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_20456,plain,
% 19.85/2.98      ( ~ r2_hidden(sK2(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),k2_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | ~ r1_tarski(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5))
% 19.85/2.98      | k2_orders_2(sK5,k1_struct_0(sK5)) = u1_struct_0(sK5) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_276]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_20448,plain,
% 19.85/2.98      ( ~ r2_hidden(sK2(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)),u1_struct_0(sK5))
% 19.85/2.98      | ~ r1_tarski(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | u1_struct_0(sK5) = k2_orders_2(sK5,k1_struct_0(sK5)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_276]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_9,plain,
% 19.85/2.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 19.85/2.98      inference(cnf_transformation,[],[f57]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_3729,plain,
% 19.85/2.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 19.85/2.98      | r2_hidden(X0,u1_struct_0(X1))
% 19.85/2.98      | v1_xboole_0(u1_struct_0(X1)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_9]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_13118,plain,
% 19.85/2.98      ( ~ m1_subset_1(sK2(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
% 19.85/2.98      | r2_hidden(sK2(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
% 19.85/2.98      | v1_xboole_0(u1_struct_0(sK5)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_3729]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_14,plain,
% 19.85/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.85/2.98      inference(cnf_transformation,[],[f64]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_3153,plain,
% 19.85/2.98      ( ~ m1_subset_1(k2_orders_2(sK5,k1_struct_0(sK5)),k1_zfmisc_1(X0))
% 19.85/2.98      | r1_tarski(k2_orders_2(sK5,k1_struct_0(sK5)),X0) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_14]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_8926,plain,
% 19.85/2.98      ( ~ m1_subset_1(k2_orders_2(sK5,k1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
% 19.85/2.98      | r1_tarski(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_3153]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_3734,plain,
% 19.85/2.98      ( ~ r2_hidden(X0,X1)
% 19.85/2.98      | r2_hidden(X0,u1_struct_0(X2))
% 19.85/2.98      | ~ r1_tarski(X1,u1_struct_0(X2)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_2]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_7700,plain,
% 19.85/2.98      ( ~ r2_hidden(sK2(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)),k2_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | r2_hidden(sK2(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)),u1_struct_0(X0))
% 19.85/2.98      | ~ r1_tarski(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(X0)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_3734]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_7702,plain,
% 19.85/2.98      ( ~ r2_hidden(sK2(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)),k2_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | r2_hidden(sK2(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)),u1_struct_0(sK5))
% 19.85/2.98      | ~ r1_tarski(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_7700]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_370,plain,( X0 = X0 ),theory(equality) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_3635,plain,
% 19.85/2.98      ( X0 != X1 | X1 = X0 ),
% 19.85/2.98      inference(resolution,[status(thm)],[c_371,c_370]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_4,plain,
% 19.85/2.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 19.85/2.98      inference(cnf_transformation,[],[f55]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_3856,plain,
% 19.85/2.98      ( ~ v1_xboole_0(X0) | X0 = k1_xboole_0 ),
% 19.85/2.98      inference(resolution,[status(thm)],[c_3635,c_4]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_3884,plain,
% 19.85/2.98      ( ~ v1_xboole_0(X0) | X0 = X1 | X1 != k1_xboole_0 ),
% 19.85/2.98      inference(resolution,[status(thm)],[c_3856,c_371]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_5789,plain,
% 19.85/2.98      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 19.85/2.98      inference(resolution,[status(thm)],[c_3884,c_3856]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_26,negated_conjecture,
% 19.85/2.98      ( u1_struct_0(sK5) != k2_orders_2(sK5,k1_struct_0(sK5)) ),
% 19.85/2.98      inference(cnf_transformation,[],[f82]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_5804,plain,
% 19.85/2.98      ( ~ v1_xboole_0(k2_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 19.85/2.98      inference(resolution,[status(thm)],[c_5789,c_26]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_4734,plain,
% 19.85/2.98      ( sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) = sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_370]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_3794,plain,
% 19.85/2.98      ( ~ r2_hidden(sK0(k1_struct_0(X0),u1_struct_0(X1)),k1_struct_0(X0))
% 19.85/2.98      | ~ v1_xboole_0(k1_struct_0(X0)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_2252]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_3800,plain,
% 19.85/2.98      ( ~ r2_hidden(sK0(k1_struct_0(sK5),u1_struct_0(sK5)),k1_struct_0(sK5))
% 19.85/2.98      | ~ v1_xboole_0(k1_struct_0(sK5)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_3794]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_1,plain,
% 19.85/2.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 19.85/2.98      inference(cnf_transformation,[],[f52]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_1703,plain,
% 19.85/2.98      ( r2_hidden(sK0(X0,u1_struct_0(X1)),X0)
% 19.85/2.98      | r1_tarski(X0,u1_struct_0(X1)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_1]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_3793,plain,
% 19.85/2.98      ( r2_hidden(sK0(k1_struct_0(X0),u1_struct_0(X1)),k1_struct_0(X0))
% 19.85/2.98      | r1_tarski(k1_struct_0(X0),u1_struct_0(X1)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_1703]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_3796,plain,
% 19.85/2.98      ( r2_hidden(sK0(k1_struct_0(sK5),u1_struct_0(sK5)),k1_struct_0(sK5))
% 19.85/2.98      | r1_tarski(k1_struct_0(sK5),u1_struct_0(sK5)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_3793]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_8,plain,
% 19.85/2.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 19.85/2.98      inference(cnf_transformation,[],[f58]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_313,plain,
% 19.85/2.98      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 19.85/2.98      inference(global_propositional_subsumption,[status(thm)],[c_8,c_5]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_314,plain,
% 19.85/2.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 19.85/2.98      inference(renaming,[status(thm)],[c_313]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_2344,plain,
% 19.85/2.98      ( m1_subset_1(X0,u1_struct_0(X1))
% 19.85/2.98      | ~ r2_hidden(X0,u1_struct_0(X1)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_314]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_3745,plain,
% 19.85/2.98      ( m1_subset_1(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
% 19.85/2.98      | ~ r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_2344]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_3036,plain,
% 19.85/2.98      ( k2_orders_2(sK5,k1_struct_0(sK5)) = k2_orders_2(sK5,k1_struct_0(sK5)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_370]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_0,plain,
% 19.85/2.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 19.85/2.98      inference(cnf_transformation,[],[f53]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_2368,plain,
% 19.85/2.98      ( ~ r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),k2_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | r1_tarski(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_0]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_1557,plain,
% 19.85/2.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.98      | ~ r1_tarski(X0,u1_struct_0(X1)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_13]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_2084,plain,
% 19.85/2.98      ( m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.98      | ~ r1_tarski(k1_struct_0(X0),u1_struct_0(X1)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_1557]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_2086,plain,
% 19.85/2.98      ( m1_subset_1(k1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 19.85/2.98      | ~ r1_tarski(k1_struct_0(sK5),u1_struct_0(sK5)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_2084]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_12,plain,
% 19.85/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.85/2.98      | m1_subset_1(sK2(X1,X0),X1)
% 19.85/2.98      | X0 = X1 ),
% 19.85/2.98      inference(cnf_transformation,[],[f62]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_277,plain,
% 19.85/2.98      ( m1_subset_1(sK2(X0,X1),X0) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 19.85/2.98      inference(bin_hyper_res,[status(thm)],[c_12,c_214]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_1853,plain,
% 19.85/2.98      ( m1_subset_1(sK2(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
% 19.85/2.98      | ~ r1_tarski(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5))
% 19.85/2.98      | k2_orders_2(sK5,k1_struct_0(sK5)) = u1_struct_0(sK5) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_277]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_1846,plain,
% 19.85/2.98      ( r2_hidden(sK0(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))),u1_struct_0(sK5))
% 19.85/2.98      | r1_tarski(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5))) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_1]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_17,plain,
% 19.85/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.98      | v2_struct_0(X1)
% 19.85/2.98      | ~ v3_orders_2(X1)
% 19.85/2.98      | ~ v4_orders_2(X1)
% 19.85/2.98      | ~ v5_orders_2(X1)
% 19.85/2.98      | ~ l1_orders_2(X1)
% 19.85/2.98      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 19.85/2.98      inference(cnf_transformation,[],[f68]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_1688,plain,
% 19.85/2.98      ( ~ m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.98      | v2_struct_0(X1)
% 19.85/2.98      | ~ v3_orders_2(X1)
% 19.85/2.98      | ~ v4_orders_2(X1)
% 19.85/2.98      | ~ v5_orders_2(X1)
% 19.85/2.98      | ~ l1_orders_2(X1)
% 19.85/2.98      | a_2_1_orders_2(X1,k1_struct_0(X0)) = k2_orders_2(X1,k1_struct_0(X0)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_17]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_1699,plain,
% 19.85/2.98      ( ~ m1_subset_1(k1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 19.85/2.98      | v2_struct_0(sK5)
% 19.85/2.98      | ~ v3_orders_2(sK5)
% 19.85/2.98      | ~ v4_orders_2(sK5)
% 19.85/2.98      | ~ v5_orders_2(sK5)
% 19.85/2.98      | ~ l1_orders_2(sK5)
% 19.85/2.98      | a_2_1_orders_2(sK5,k1_struct_0(sK5)) = k2_orders_2(sK5,k1_struct_0(sK5)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_1688]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_18,plain,
% 19.85/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.98      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.98      | v2_struct_0(X1)
% 19.85/2.98      | ~ v3_orders_2(X1)
% 19.85/2.98      | ~ v4_orders_2(X1)
% 19.85/2.98      | ~ v5_orders_2(X1)
% 19.85/2.98      | ~ l1_orders_2(X1) ),
% 19.85/2.98      inference(cnf_transformation,[],[f69]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_1689,plain,
% 19.85/2.98      ( m1_subset_1(k2_orders_2(X0,k1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X0)))
% 19.85/2.98      | ~ m1_subset_1(k1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
% 19.85/2.98      | v2_struct_0(X0)
% 19.85/2.98      | ~ v3_orders_2(X0)
% 19.85/2.98      | ~ v4_orders_2(X0)
% 19.85/2.98      | ~ v5_orders_2(X0)
% 19.85/2.98      | ~ l1_orders_2(X0) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_18]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_1695,plain,
% 19.85/2.98      ( m1_subset_1(k2_orders_2(sK5,k1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
% 19.85/2.98      | ~ m1_subset_1(k1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 19.85/2.98      | v2_struct_0(sK5)
% 19.85/2.98      | ~ v3_orders_2(sK5)
% 19.85/2.98      | ~ v4_orders_2(sK5)
% 19.85/2.98      | ~ v5_orders_2(sK5)
% 19.85/2.98      | ~ l1_orders_2(sK5) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_1689]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_1470,plain,
% 19.85/2.98      ( k2_orders_2(sK5,k1_struct_0(sK5)) != X0
% 19.85/2.98      | u1_struct_0(sK5) != X0
% 19.85/2.98      | u1_struct_0(sK5) = k2_orders_2(sK5,k1_struct_0(sK5)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_371]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_1639,plain,
% 19.85/2.98      ( k2_orders_2(sK5,k1_struct_0(sK5)) != u1_struct_0(sK5)
% 19.85/2.98      | u1_struct_0(sK5) = k2_orders_2(sK5,k1_struct_0(sK5))
% 19.85/2.98      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_1470]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_1623,plain,
% 19.85/2.98      ( ~ m1_subset_1(sK2(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)),k2_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | r2_hidden(sK2(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)),k2_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | v1_xboole_0(k2_orders_2(sK5,k1_struct_0(sK5))) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_9]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_1620,plain,
% 19.85/2.98      ( m1_subset_1(sK2(k2_orders_2(sK5,k1_struct_0(sK5)),u1_struct_0(sK5)),k2_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | ~ r1_tarski(u1_struct_0(sK5),k2_orders_2(sK5,k1_struct_0(sK5)))
% 19.85/2.98      | u1_struct_0(sK5) = k2_orders_2(sK5,k1_struct_0(sK5)) ),
% 19.85/2.98      inference(instantiation,[status(thm)],[c_277]) ).
% 19.85/2.98  
% 19.85/2.98  cnf(c_399,plain,
% 19.85/2.98      ( sK5 = sK5 ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_370]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_378,plain,
% 19.85/2.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 19.85/2.99      theory(equality) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_391,plain,
% 19.85/2.99      ( u1_struct_0(sK5) = u1_struct_0(sK5) | sK5 != sK5 ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_378]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_16,plain,
% 19.85/2.99      ( ~ l1_struct_0(X0) | v1_xboole_0(k1_struct_0(X0)) ),
% 19.85/2.99      inference(cnf_transformation,[],[f67]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_65,plain,
% 19.85/2.99      ( ~ l1_struct_0(sK5) | v1_xboole_0(k1_struct_0(sK5)) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_16]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_19,plain,
% 19.85/2.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 19.85/2.99      inference(cnf_transformation,[],[f70]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_56,plain,
% 19.85/2.99      ( ~ l1_orders_2(sK5) | l1_struct_0(sK5) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_19]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_27,negated_conjecture,
% 19.85/2.99      ( l1_orders_2(sK5) ),
% 19.85/2.99      inference(cnf_transformation,[],[f81]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_28,negated_conjecture,
% 19.85/2.99      ( v5_orders_2(sK5) ),
% 19.85/2.99      inference(cnf_transformation,[],[f80]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_29,negated_conjecture,
% 19.85/2.99      ( v4_orders_2(sK5) ),
% 19.85/2.99      inference(cnf_transformation,[],[f79]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_30,negated_conjecture,
% 19.85/2.99      ( v3_orders_2(sK5) ),
% 19.85/2.99      inference(cnf_transformation,[],[f78]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_31,negated_conjecture,
% 19.85/2.99      ( ~ v2_struct_0(sK5) ),
% 19.85/2.99      inference(cnf_transformation,[],[f77]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(contradiction,plain,
% 19.85/2.99      ( $false ),
% 19.85/2.99      inference(minisat,
% 19.85/2.99                [status(thm)],
% 19.85/2.99                [c_71177,c_57619,c_57615,c_51638,c_28933,c_20456,c_20448,
% 19.85/2.99                 c_13118,c_8926,c_7702,c_5804,c_4734,c_3800,c_3796,
% 19.85/2.99                 c_3745,c_3036,c_2368,c_2086,c_1853,c_1846,c_1699,c_1695,
% 19.85/2.99                 c_1639,c_1623,c_1620,c_399,c_391,c_65,c_56,c_26,c_27,
% 19.85/2.99                 c_28,c_29,c_30,c_31]) ).
% 19.85/2.99  
% 19.85/2.99  
% 19.85/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.85/2.99  
% 19.85/2.99  ------                               Statistics
% 19.85/2.99  
% 19.85/2.99  ------ Selected
% 19.85/2.99  
% 19.85/2.99  total_time:                             2.266
% 19.85/2.99  
%------------------------------------------------------------------------------
