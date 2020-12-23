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
% DateTime   : Thu Dec  3 12:12:09 EST 2020

% Result     : Theorem 11.45s
% Output     : CNFRefutation 11.45s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 671 expanded)
%              Number of clauses        :   84 ( 199 expanded)
%              Number of leaves         :   21 ( 140 expanded)
%              Depth                    :   19
%              Number of atoms          :  596 (3185 expanded)
%              Number of equality atoms :  148 ( 551 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
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

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
        & r2_hidden(sK2(X1,X2,X3),X2)
        & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
                & r2_hidden(sK2(X1,X2,X3),X2)
                & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK3(X0,X1,X2) = X0
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f51,f53,f52])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | r2_hidden(sK2(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f96,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_orders_2(X1,X2))
      | r2_hidden(sK2(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f85])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f37,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f55,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( u1_struct_0(sK4) != k2_orders_2(sK4,k1_struct_0(sK4))
      & l1_orders_2(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( u1_struct_0(sK4) != k2_orders_2(sK4,k1_struct_0(sK4))
    & l1_orders_2(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f55])).

fof(f90,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f77,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f80,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f92,plain,(
    u1_struct_0(sK4) != k2_orders_2(sK4,k1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1264,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1256,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3292,plain,
    ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_1256])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1259,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_32,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,a_2_1_orders_2(sK4,X1))
    | r2_hidden(sK2(sK4,X1,X0),X1)
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_34,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_33,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_31,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,a_2_1_orders_2(sK4,X1))
    | r2_hidden(sK2(sK4,X1,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_35,c_34,c_33,c_31])).

cnf(c_1243,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK4,X1)) = iProver_top
    | r2_hidden(sK2(sK4,X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1248,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2451,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK4,X1)) = iProver_top
    | r1_tarski(X1,sK2(sK4,X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1243,c_1248])).

cnf(c_2695,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK4,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1259,c_2451])).

cnf(c_12,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1254,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_579,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | a_2_1_orders_2(sK4,X0) = k2_orders_2(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | a_2_1_orders_2(sK4,X0) = k2_orders_2(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_580,c_35,c_34,c_33,c_31])).

cnf(c_1241,plain,
    ( a_2_1_orders_2(sK4,X0) = k2_orders_2(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_1863,plain,
    ( a_2_1_orders_2(sK4,k1_xboole_0) = k2_orders_2(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1254,c_1241])).

cnf(c_2696,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK4,k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2695,c_1863])).

cnf(c_1509,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1515,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1509])).

cnf(c_22749,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK4,k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2696,c_1515])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1265,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_22757,plain,
    ( m1_subset_1(sK0(X0,k2_orders_2(sK4,k1_xboole_0)),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(X0,k2_orders_2(sK4,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22749,c_1265])).

cnf(c_22984,plain,
    ( r1_tarski(u1_struct_0(sK4),k2_orders_2(sK4,k1_xboole_0)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3292,c_22757])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_562,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k2_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k2_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_562,c_35,c_34,c_33,c_31])).

cnf(c_1242,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k2_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_566])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1250,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4722,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK4,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1250])).

cnf(c_5161,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,k2_orders_2(sK4,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_4722])).

cnf(c_9439,plain,
    ( m1_subset_1(sK0(k2_orders_2(sK4,k1_xboole_0),X0),u1_struct_0(sK4)) = iProver_top
    | r1_tarski(k2_orders_2(sK4,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_5161])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1255,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10090,plain,
    ( r2_hidden(sK0(k2_orders_2(sK4,k1_xboole_0),X0),u1_struct_0(sK4)) = iProver_top
    | r1_tarski(k2_orders_2(sK4,k1_xboole_0),X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9439,c_1255])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1249,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4640,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,k2_orders_2(sK4,X0)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1249])).

cnf(c_5115,plain,
    ( r2_hidden(X0,k2_orders_2(sK4,k1_xboole_0)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_4640])).

cnf(c_8747,plain,
    ( r1_tarski(k2_orders_2(sK4,k1_xboole_0),X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_5115])).

cnf(c_12242,plain,
    ( r1_tarski(k2_orders_2(sK4,k1_xboole_0),X0) = iProver_top
    | r2_hidden(sK0(k2_orders_2(sK4,k1_xboole_0),X0),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10090,c_8747])).

cnf(c_12243,plain,
    ( r2_hidden(sK0(k2_orders_2(sK4,k1_xboole_0),X0),u1_struct_0(sK4)) = iProver_top
    | r1_tarski(k2_orders_2(sK4,k1_xboole_0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_12242])).

cnf(c_12250,plain,
    ( r1_tarski(k2_orders_2(sK4,k1_xboole_0),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12243,c_1265])).

cnf(c_22761,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(k2_orders_2(sK4,k1_xboole_0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22749,c_1248])).

cnf(c_22909,plain,
    ( m1_subset_1(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12250,c_22761])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2382,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_8587,plain,
    ( m1_subset_1(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2382])).

cnf(c_8588,plain,
    ( m1_subset_1(u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8587])).

cnf(c_811,plain,
    ( X0 != X1
    | X2 != X3
    | k2_orders_2(X0,X2) = k2_orders_2(X1,X3) ),
    theory(equality)).

cnf(c_2761,plain,
    ( k2_orders_2(sK4,k1_struct_0(sK4)) = k2_orders_2(X0,X1)
    | k1_struct_0(sK4) != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_6645,plain,
    ( k2_orders_2(sK4,k1_struct_0(sK4)) = k2_orders_2(X0,k1_xboole_0)
    | k1_struct_0(sK4) != k1_xboole_0
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2761])).

cnf(c_6646,plain,
    ( k2_orders_2(sK4,k1_struct_0(sK4)) = k2_orders_2(sK4,k1_xboole_0)
    | k1_struct_0(sK4) != k1_xboole_0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_6645])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1918,plain,
    ( ~ r1_tarski(X0,k2_orders_2(sK4,k1_xboole_0))
    | ~ r1_tarski(k2_orders_2(sK4,k1_xboole_0),X0)
    | X0 = k2_orders_2(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6524,plain,
    ( ~ r1_tarski(k2_orders_2(sK4,k1_xboole_0),u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),k2_orders_2(sK4,k1_xboole_0))
    | u1_struct_0(sK4) = k2_orders_2(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1918])).

cnf(c_6532,plain,
    ( u1_struct_0(sK4) = k2_orders_2(sK4,k1_xboole_0)
    | r1_tarski(k2_orders_2(sK4,k1_xboole_0),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(u1_struct_0(sK4),k2_orders_2(sK4,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6524])).

cnf(c_804,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1472,plain,
    ( k2_orders_2(sK4,k1_struct_0(sK4)) != X0
    | u1_struct_0(sK4) != X0
    | u1_struct_0(sK4) = k2_orders_2(sK4,k1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_5345,plain,
    ( k2_orders_2(sK4,k1_struct_0(sK4)) != k2_orders_2(sK4,k1_xboole_0)
    | u1_struct_0(sK4) = k2_orders_2(sK4,k1_struct_0(sK4))
    | u1_struct_0(sK4) != k2_orders_2(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1472])).

cnf(c_111,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_107,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_20,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_69,plain,
    ( ~ l1_struct_0(sK4)
    | k1_struct_0(sK4) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_23,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_60,plain,
    ( ~ l1_orders_2(sK4)
    | l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_30,negated_conjecture,
    ( u1_struct_0(sK4) != k2_orders_2(sK4,k1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f92])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22984,c_22909,c_12250,c_8588,c_6646,c_6532,c_5345,c_111,c_107,c_69,c_60,c_30,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:49:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.45/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.45/2.00  
% 11.45/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.45/2.00  
% 11.45/2.00  ------  iProver source info
% 11.45/2.00  
% 11.45/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.45/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.45/2.00  git: non_committed_changes: false
% 11.45/2.00  git: last_make_outside_of_git: false
% 11.45/2.00  
% 11.45/2.00  ------ 
% 11.45/2.00  
% 11.45/2.00  ------ Input Options
% 11.45/2.00  
% 11.45/2.00  --out_options                           all
% 11.45/2.00  --tptp_safe_out                         true
% 11.45/2.00  --problem_path                          ""
% 11.45/2.00  --include_path                          ""
% 11.45/2.00  --clausifier                            res/vclausify_rel
% 11.45/2.00  --clausifier_options                    --mode clausify
% 11.45/2.00  --stdin                                 false
% 11.45/2.00  --stats_out                             all
% 11.45/2.00  
% 11.45/2.00  ------ General Options
% 11.45/2.00  
% 11.45/2.00  --fof                                   false
% 11.45/2.00  --time_out_real                         305.
% 11.45/2.00  --time_out_virtual                      -1.
% 11.45/2.00  --symbol_type_check                     false
% 11.45/2.00  --clausify_out                          false
% 11.45/2.00  --sig_cnt_out                           false
% 11.45/2.00  --trig_cnt_out                          false
% 11.45/2.00  --trig_cnt_out_tolerance                1.
% 11.45/2.00  --trig_cnt_out_sk_spl                   false
% 11.45/2.00  --abstr_cl_out                          false
% 11.45/2.00  
% 11.45/2.00  ------ Global Options
% 11.45/2.00  
% 11.45/2.00  --schedule                              default
% 11.45/2.00  --add_important_lit                     false
% 11.45/2.00  --prop_solver_per_cl                    1000
% 11.45/2.00  --min_unsat_core                        false
% 11.45/2.00  --soft_assumptions                      false
% 11.45/2.00  --soft_lemma_size                       3
% 11.45/2.00  --prop_impl_unit_size                   0
% 11.45/2.00  --prop_impl_unit                        []
% 11.45/2.00  --share_sel_clauses                     true
% 11.45/2.00  --reset_solvers                         false
% 11.45/2.00  --bc_imp_inh                            [conj_cone]
% 11.45/2.00  --conj_cone_tolerance                   3.
% 11.45/2.00  --extra_neg_conj                        none
% 11.45/2.00  --large_theory_mode                     true
% 11.45/2.00  --prolific_symb_bound                   200
% 11.45/2.00  --lt_threshold                          2000
% 11.45/2.00  --clause_weak_htbl                      true
% 11.45/2.00  --gc_record_bc_elim                     false
% 11.45/2.00  
% 11.45/2.00  ------ Preprocessing Options
% 11.45/2.00  
% 11.45/2.00  --preprocessing_flag                    true
% 11.45/2.00  --time_out_prep_mult                    0.1
% 11.45/2.00  --splitting_mode                        input
% 11.45/2.00  --splitting_grd                         true
% 11.45/2.00  --splitting_cvd                         false
% 11.45/2.00  --splitting_cvd_svl                     false
% 11.45/2.00  --splitting_nvd                         32
% 11.45/2.00  --sub_typing                            true
% 11.45/2.00  --prep_gs_sim                           true
% 11.45/2.00  --prep_unflatten                        true
% 11.45/2.00  --prep_res_sim                          true
% 11.45/2.00  --prep_upred                            true
% 11.45/2.00  --prep_sem_filter                       exhaustive
% 11.45/2.00  --prep_sem_filter_out                   false
% 11.45/2.00  --pred_elim                             true
% 11.45/2.00  --res_sim_input                         true
% 11.45/2.00  --eq_ax_congr_red                       true
% 11.45/2.00  --pure_diseq_elim                       true
% 11.45/2.00  --brand_transform                       false
% 11.45/2.00  --non_eq_to_eq                          false
% 11.45/2.00  --prep_def_merge                        true
% 11.45/2.00  --prep_def_merge_prop_impl              false
% 11.45/2.00  --prep_def_merge_mbd                    true
% 11.45/2.00  --prep_def_merge_tr_red                 false
% 11.45/2.00  --prep_def_merge_tr_cl                  false
% 11.45/2.00  --smt_preprocessing                     true
% 11.45/2.00  --smt_ac_axioms                         fast
% 11.45/2.00  --preprocessed_out                      false
% 11.45/2.00  --preprocessed_stats                    false
% 11.45/2.00  
% 11.45/2.00  ------ Abstraction refinement Options
% 11.45/2.00  
% 11.45/2.00  --abstr_ref                             []
% 11.45/2.00  --abstr_ref_prep                        false
% 11.45/2.00  --abstr_ref_until_sat                   false
% 11.45/2.00  --abstr_ref_sig_restrict                funpre
% 11.45/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.45/2.00  --abstr_ref_under                       []
% 11.45/2.00  
% 11.45/2.00  ------ SAT Options
% 11.45/2.00  
% 11.45/2.00  --sat_mode                              false
% 11.45/2.00  --sat_fm_restart_options                ""
% 11.45/2.00  --sat_gr_def                            false
% 11.45/2.00  --sat_epr_types                         true
% 11.45/2.00  --sat_non_cyclic_types                  false
% 11.45/2.00  --sat_finite_models                     false
% 11.45/2.00  --sat_fm_lemmas                         false
% 11.45/2.00  --sat_fm_prep                           false
% 11.45/2.00  --sat_fm_uc_incr                        true
% 11.45/2.00  --sat_out_model                         small
% 11.45/2.00  --sat_out_clauses                       false
% 11.45/2.00  
% 11.45/2.00  ------ QBF Options
% 11.45/2.00  
% 11.45/2.00  --qbf_mode                              false
% 11.45/2.00  --qbf_elim_univ                         false
% 11.45/2.00  --qbf_dom_inst                          none
% 11.45/2.00  --qbf_dom_pre_inst                      false
% 11.45/2.00  --qbf_sk_in                             false
% 11.45/2.00  --qbf_pred_elim                         true
% 11.45/2.00  --qbf_split                             512
% 11.45/2.00  
% 11.45/2.00  ------ BMC1 Options
% 11.45/2.00  
% 11.45/2.00  --bmc1_incremental                      false
% 11.45/2.00  --bmc1_axioms                           reachable_all
% 11.45/2.00  --bmc1_min_bound                        0
% 11.45/2.00  --bmc1_max_bound                        -1
% 11.45/2.00  --bmc1_max_bound_default                -1
% 11.45/2.00  --bmc1_symbol_reachability              true
% 11.45/2.00  --bmc1_property_lemmas                  false
% 11.45/2.00  --bmc1_k_induction                      false
% 11.45/2.00  --bmc1_non_equiv_states                 false
% 11.45/2.00  --bmc1_deadlock                         false
% 11.45/2.00  --bmc1_ucm                              false
% 11.45/2.00  --bmc1_add_unsat_core                   none
% 11.45/2.00  --bmc1_unsat_core_children              false
% 11.45/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.45/2.00  --bmc1_out_stat                         full
% 11.45/2.00  --bmc1_ground_init                      false
% 11.45/2.00  --bmc1_pre_inst_next_state              false
% 11.45/2.00  --bmc1_pre_inst_state                   false
% 11.45/2.00  --bmc1_pre_inst_reach_state             false
% 11.45/2.00  --bmc1_out_unsat_core                   false
% 11.45/2.00  --bmc1_aig_witness_out                  false
% 11.45/2.00  --bmc1_verbose                          false
% 11.45/2.00  --bmc1_dump_clauses_tptp                false
% 11.45/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.45/2.00  --bmc1_dump_file                        -
% 11.45/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.45/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.45/2.00  --bmc1_ucm_extend_mode                  1
% 11.45/2.00  --bmc1_ucm_init_mode                    2
% 11.45/2.00  --bmc1_ucm_cone_mode                    none
% 11.45/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.45/2.00  --bmc1_ucm_relax_model                  4
% 11.45/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.45/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.45/2.00  --bmc1_ucm_layered_model                none
% 11.45/2.00  --bmc1_ucm_max_lemma_size               10
% 11.45/2.00  
% 11.45/2.00  ------ AIG Options
% 11.45/2.00  
% 11.45/2.00  --aig_mode                              false
% 11.45/2.00  
% 11.45/2.00  ------ Instantiation Options
% 11.45/2.00  
% 11.45/2.00  --instantiation_flag                    true
% 11.45/2.00  --inst_sos_flag                         false
% 11.45/2.00  --inst_sos_phase                        true
% 11.45/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.45/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.45/2.00  --inst_lit_sel_side                     num_symb
% 11.45/2.00  --inst_solver_per_active                1400
% 11.45/2.00  --inst_solver_calls_frac                1.
% 11.45/2.00  --inst_passive_queue_type               priority_queues
% 11.45/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.45/2.00  --inst_passive_queues_freq              [25;2]
% 11.45/2.00  --inst_dismatching                      true
% 11.45/2.00  --inst_eager_unprocessed_to_passive     true
% 11.45/2.00  --inst_prop_sim_given                   true
% 11.45/2.00  --inst_prop_sim_new                     false
% 11.45/2.00  --inst_subs_new                         false
% 11.45/2.00  --inst_eq_res_simp                      false
% 11.45/2.00  --inst_subs_given                       false
% 11.45/2.00  --inst_orphan_elimination               true
% 11.45/2.00  --inst_learning_loop_flag               true
% 11.45/2.00  --inst_learning_start                   3000
% 11.45/2.00  --inst_learning_factor                  2
% 11.45/2.00  --inst_start_prop_sim_after_learn       3
% 11.45/2.00  --inst_sel_renew                        solver
% 11.45/2.00  --inst_lit_activity_flag                true
% 11.45/2.00  --inst_restr_to_given                   false
% 11.45/2.00  --inst_activity_threshold               500
% 11.45/2.00  --inst_out_proof                        true
% 11.45/2.00  
% 11.45/2.00  ------ Resolution Options
% 11.45/2.00  
% 11.45/2.00  --resolution_flag                       true
% 11.45/2.00  --res_lit_sel                           adaptive
% 11.45/2.00  --res_lit_sel_side                      none
% 11.45/2.00  --res_ordering                          kbo
% 11.45/2.00  --res_to_prop_solver                    active
% 11.45/2.00  --res_prop_simpl_new                    false
% 11.45/2.00  --res_prop_simpl_given                  true
% 11.45/2.00  --res_passive_queue_type                priority_queues
% 11.45/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.45/2.00  --res_passive_queues_freq               [15;5]
% 11.45/2.00  --res_forward_subs                      full
% 11.45/2.00  --res_backward_subs                     full
% 11.45/2.00  --res_forward_subs_resolution           true
% 11.45/2.00  --res_backward_subs_resolution          true
% 11.45/2.00  --res_orphan_elimination                true
% 11.45/2.00  --res_time_limit                        2.
% 11.45/2.00  --res_out_proof                         true
% 11.45/2.00  
% 11.45/2.00  ------ Superposition Options
% 11.45/2.00  
% 11.45/2.00  --superposition_flag                    true
% 11.45/2.00  --sup_passive_queue_type                priority_queues
% 11.45/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.45/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.45/2.00  --demod_completeness_check              fast
% 11.45/2.00  --demod_use_ground                      true
% 11.45/2.00  --sup_to_prop_solver                    passive
% 11.45/2.00  --sup_prop_simpl_new                    true
% 11.45/2.00  --sup_prop_simpl_given                  true
% 11.45/2.00  --sup_fun_splitting                     false
% 11.45/2.00  --sup_smt_interval                      50000
% 11.45/2.00  
% 11.45/2.00  ------ Superposition Simplification Setup
% 11.45/2.00  
% 11.45/2.00  --sup_indices_passive                   []
% 11.45/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.45/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.45/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.45/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.45/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.45/2.00  --sup_full_bw                           [BwDemod]
% 11.45/2.00  --sup_immed_triv                        [TrivRules]
% 11.45/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.45/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.45/2.00  --sup_immed_bw_main                     []
% 11.45/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.45/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.45/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.45/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.45/2.00  
% 11.45/2.00  ------ Combination Options
% 11.45/2.00  
% 11.45/2.00  --comb_res_mult                         3
% 11.45/2.00  --comb_sup_mult                         2
% 11.45/2.00  --comb_inst_mult                        10
% 11.45/2.00  
% 11.45/2.00  ------ Debug Options
% 11.45/2.00  
% 11.45/2.00  --dbg_backtrace                         false
% 11.45/2.00  --dbg_dump_prop_clauses                 false
% 11.45/2.00  --dbg_dump_prop_clauses_file            -
% 11.45/2.00  --dbg_out_stat                          false
% 11.45/2.00  ------ Parsing...
% 11.45/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.45/2.00  
% 11.45/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 11.45/2.00  
% 11.45/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.45/2.00  
% 11.45/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.45/2.00  ------ Proving...
% 11.45/2.00  ------ Problem Properties 
% 11.45/2.00  
% 11.45/2.00  
% 11.45/2.00  clauses                                 27
% 11.45/2.00  conjectures                             1
% 11.45/2.00  EPR                                     10
% 11.45/2.00  Horn                                    20
% 11.45/2.00  unary                                   6
% 11.45/2.00  binary                                  5
% 11.45/2.00  lits                                    73
% 11.45/2.00  lits eq                                 8
% 11.45/2.00  fd_pure                                 0
% 11.45/2.00  fd_pseudo                               0
% 11.45/2.00  fd_cond                                 0
% 11.45/2.00  fd_pseudo_cond                          4
% 11.45/2.00  AC symbols                              0
% 11.45/2.00  
% 11.45/2.00  ------ Schedule dynamic 5 is on 
% 11.45/2.00  
% 11.45/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.45/2.00  
% 11.45/2.00  
% 11.45/2.00  ------ 
% 11.45/2.00  Current options:
% 11.45/2.00  ------ 
% 11.45/2.00  
% 11.45/2.00  ------ Input Options
% 11.45/2.00  
% 11.45/2.00  --out_options                           all
% 11.45/2.00  --tptp_safe_out                         true
% 11.45/2.00  --problem_path                          ""
% 11.45/2.00  --include_path                          ""
% 11.45/2.00  --clausifier                            res/vclausify_rel
% 11.45/2.00  --clausifier_options                    --mode clausify
% 11.45/2.00  --stdin                                 false
% 11.45/2.00  --stats_out                             all
% 11.45/2.00  
% 11.45/2.00  ------ General Options
% 11.45/2.00  
% 11.45/2.00  --fof                                   false
% 11.45/2.00  --time_out_real                         305.
% 11.45/2.00  --time_out_virtual                      -1.
% 11.45/2.00  --symbol_type_check                     false
% 11.45/2.00  --clausify_out                          false
% 11.45/2.00  --sig_cnt_out                           false
% 11.45/2.00  --trig_cnt_out                          false
% 11.45/2.00  --trig_cnt_out_tolerance                1.
% 11.45/2.00  --trig_cnt_out_sk_spl                   false
% 11.45/2.00  --abstr_cl_out                          false
% 11.45/2.00  
% 11.45/2.00  ------ Global Options
% 11.45/2.00  
% 11.45/2.00  --schedule                              default
% 11.45/2.00  --add_important_lit                     false
% 11.45/2.00  --prop_solver_per_cl                    1000
% 11.45/2.00  --min_unsat_core                        false
% 11.45/2.00  --soft_assumptions                      false
% 11.45/2.00  --soft_lemma_size                       3
% 11.45/2.00  --prop_impl_unit_size                   0
% 11.45/2.00  --prop_impl_unit                        []
% 11.45/2.00  --share_sel_clauses                     true
% 11.45/2.00  --reset_solvers                         false
% 11.45/2.00  --bc_imp_inh                            [conj_cone]
% 11.45/2.00  --conj_cone_tolerance                   3.
% 11.45/2.00  --extra_neg_conj                        none
% 11.45/2.00  --large_theory_mode                     true
% 11.45/2.00  --prolific_symb_bound                   200
% 11.45/2.00  --lt_threshold                          2000
% 11.45/2.00  --clause_weak_htbl                      true
% 11.45/2.00  --gc_record_bc_elim                     false
% 11.45/2.00  
% 11.45/2.00  ------ Preprocessing Options
% 11.45/2.00  
% 11.45/2.00  --preprocessing_flag                    true
% 11.45/2.00  --time_out_prep_mult                    0.1
% 11.45/2.00  --splitting_mode                        input
% 11.45/2.00  --splitting_grd                         true
% 11.45/2.00  --splitting_cvd                         false
% 11.45/2.00  --splitting_cvd_svl                     false
% 11.45/2.00  --splitting_nvd                         32
% 11.45/2.00  --sub_typing                            true
% 11.45/2.00  --prep_gs_sim                           true
% 11.45/2.00  --prep_unflatten                        true
% 11.45/2.00  --prep_res_sim                          true
% 11.45/2.00  --prep_upred                            true
% 11.45/2.00  --prep_sem_filter                       exhaustive
% 11.45/2.00  --prep_sem_filter_out                   false
% 11.45/2.00  --pred_elim                             true
% 11.45/2.00  --res_sim_input                         true
% 11.45/2.00  --eq_ax_congr_red                       true
% 11.45/2.00  --pure_diseq_elim                       true
% 11.45/2.00  --brand_transform                       false
% 11.45/2.00  --non_eq_to_eq                          false
% 11.45/2.00  --prep_def_merge                        true
% 11.45/2.00  --prep_def_merge_prop_impl              false
% 11.45/2.00  --prep_def_merge_mbd                    true
% 11.45/2.00  --prep_def_merge_tr_red                 false
% 11.45/2.00  --prep_def_merge_tr_cl                  false
% 11.45/2.00  --smt_preprocessing                     true
% 11.45/2.00  --smt_ac_axioms                         fast
% 11.45/2.00  --preprocessed_out                      false
% 11.45/2.00  --preprocessed_stats                    false
% 11.45/2.00  
% 11.45/2.00  ------ Abstraction refinement Options
% 11.45/2.00  
% 11.45/2.00  --abstr_ref                             []
% 11.45/2.00  --abstr_ref_prep                        false
% 11.45/2.00  --abstr_ref_until_sat                   false
% 11.45/2.00  --abstr_ref_sig_restrict                funpre
% 11.45/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.45/2.00  --abstr_ref_under                       []
% 11.45/2.00  
% 11.45/2.00  ------ SAT Options
% 11.45/2.00  
% 11.45/2.00  --sat_mode                              false
% 11.45/2.00  --sat_fm_restart_options                ""
% 11.45/2.00  --sat_gr_def                            false
% 11.45/2.00  --sat_epr_types                         true
% 11.45/2.00  --sat_non_cyclic_types                  false
% 11.45/2.00  --sat_finite_models                     false
% 11.45/2.00  --sat_fm_lemmas                         false
% 11.45/2.00  --sat_fm_prep                           false
% 11.45/2.00  --sat_fm_uc_incr                        true
% 11.45/2.00  --sat_out_model                         small
% 11.45/2.00  --sat_out_clauses                       false
% 11.45/2.00  
% 11.45/2.00  ------ QBF Options
% 11.45/2.00  
% 11.45/2.00  --qbf_mode                              false
% 11.45/2.00  --qbf_elim_univ                         false
% 11.45/2.00  --qbf_dom_inst                          none
% 11.45/2.00  --qbf_dom_pre_inst                      false
% 11.45/2.00  --qbf_sk_in                             false
% 11.45/2.00  --qbf_pred_elim                         true
% 11.45/2.00  --qbf_split                             512
% 11.45/2.00  
% 11.45/2.00  ------ BMC1 Options
% 11.45/2.00  
% 11.45/2.00  --bmc1_incremental                      false
% 11.45/2.00  --bmc1_axioms                           reachable_all
% 11.45/2.00  --bmc1_min_bound                        0
% 11.45/2.00  --bmc1_max_bound                        -1
% 11.45/2.00  --bmc1_max_bound_default                -1
% 11.45/2.00  --bmc1_symbol_reachability              true
% 11.45/2.00  --bmc1_property_lemmas                  false
% 11.45/2.00  --bmc1_k_induction                      false
% 11.45/2.00  --bmc1_non_equiv_states                 false
% 11.45/2.00  --bmc1_deadlock                         false
% 11.45/2.00  --bmc1_ucm                              false
% 11.45/2.00  --bmc1_add_unsat_core                   none
% 11.45/2.00  --bmc1_unsat_core_children              false
% 11.45/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.45/2.00  --bmc1_out_stat                         full
% 11.45/2.00  --bmc1_ground_init                      false
% 11.45/2.00  --bmc1_pre_inst_next_state              false
% 11.45/2.00  --bmc1_pre_inst_state                   false
% 11.45/2.00  --bmc1_pre_inst_reach_state             false
% 11.45/2.00  --bmc1_out_unsat_core                   false
% 11.45/2.00  --bmc1_aig_witness_out                  false
% 11.45/2.00  --bmc1_verbose                          false
% 11.45/2.00  --bmc1_dump_clauses_tptp                false
% 11.45/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.45/2.00  --bmc1_dump_file                        -
% 11.45/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.45/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.45/2.00  --bmc1_ucm_extend_mode                  1
% 11.45/2.00  --bmc1_ucm_init_mode                    2
% 11.45/2.00  --bmc1_ucm_cone_mode                    none
% 11.45/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.45/2.00  --bmc1_ucm_relax_model                  4
% 11.45/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.45/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.45/2.00  --bmc1_ucm_layered_model                none
% 11.45/2.00  --bmc1_ucm_max_lemma_size               10
% 11.45/2.00  
% 11.45/2.00  ------ AIG Options
% 11.45/2.00  
% 11.45/2.00  --aig_mode                              false
% 11.45/2.00  
% 11.45/2.00  ------ Instantiation Options
% 11.45/2.00  
% 11.45/2.00  --instantiation_flag                    true
% 11.45/2.00  --inst_sos_flag                         false
% 11.45/2.00  --inst_sos_phase                        true
% 11.45/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.45/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.45/2.00  --inst_lit_sel_side                     none
% 11.45/2.00  --inst_solver_per_active                1400
% 11.45/2.00  --inst_solver_calls_frac                1.
% 11.45/2.00  --inst_passive_queue_type               priority_queues
% 11.45/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.45/2.00  --inst_passive_queues_freq              [25;2]
% 11.45/2.00  --inst_dismatching                      true
% 11.45/2.00  --inst_eager_unprocessed_to_passive     true
% 11.45/2.00  --inst_prop_sim_given                   true
% 11.45/2.00  --inst_prop_sim_new                     false
% 11.45/2.00  --inst_subs_new                         false
% 11.45/2.00  --inst_eq_res_simp                      false
% 11.45/2.00  --inst_subs_given                       false
% 11.45/2.00  --inst_orphan_elimination               true
% 11.45/2.00  --inst_learning_loop_flag               true
% 11.45/2.00  --inst_learning_start                   3000
% 11.45/2.00  --inst_learning_factor                  2
% 11.45/2.00  --inst_start_prop_sim_after_learn       3
% 11.45/2.00  --inst_sel_renew                        solver
% 11.45/2.00  --inst_lit_activity_flag                true
% 11.45/2.00  --inst_restr_to_given                   false
% 11.45/2.00  --inst_activity_threshold               500
% 11.45/2.00  --inst_out_proof                        true
% 11.45/2.00  
% 11.45/2.00  ------ Resolution Options
% 11.45/2.00  
% 11.45/2.00  --resolution_flag                       false
% 11.45/2.00  --res_lit_sel                           adaptive
% 11.45/2.00  --res_lit_sel_side                      none
% 11.45/2.00  --res_ordering                          kbo
% 11.45/2.00  --res_to_prop_solver                    active
% 11.45/2.00  --res_prop_simpl_new                    false
% 11.45/2.00  --res_prop_simpl_given                  true
% 11.45/2.00  --res_passive_queue_type                priority_queues
% 11.45/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.45/2.00  --res_passive_queues_freq               [15;5]
% 11.45/2.00  --res_forward_subs                      full
% 11.45/2.00  --res_backward_subs                     full
% 11.45/2.00  --res_forward_subs_resolution           true
% 11.45/2.00  --res_backward_subs_resolution          true
% 11.45/2.00  --res_orphan_elimination                true
% 11.45/2.00  --res_time_limit                        2.
% 11.45/2.00  --res_out_proof                         true
% 11.45/2.00  
% 11.45/2.00  ------ Superposition Options
% 11.45/2.00  
% 11.45/2.00  --superposition_flag                    true
% 11.45/2.00  --sup_passive_queue_type                priority_queues
% 11.45/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.45/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.45/2.00  --demod_completeness_check              fast
% 11.45/2.00  --demod_use_ground                      true
% 11.45/2.00  --sup_to_prop_solver                    passive
% 11.45/2.00  --sup_prop_simpl_new                    true
% 11.45/2.00  --sup_prop_simpl_given                  true
% 11.45/2.00  --sup_fun_splitting                     false
% 11.45/2.00  --sup_smt_interval                      50000
% 11.45/2.00  
% 11.45/2.00  ------ Superposition Simplification Setup
% 11.45/2.00  
% 11.45/2.00  --sup_indices_passive                   []
% 11.45/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.45/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.45/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.45/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.45/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.45/2.00  --sup_full_bw                           [BwDemod]
% 11.45/2.00  --sup_immed_triv                        [TrivRules]
% 11.45/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.45/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.45/2.00  --sup_immed_bw_main                     []
% 11.45/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.45/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.45/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.45/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.45/2.00  
% 11.45/2.00  ------ Combination Options
% 11.45/2.00  
% 11.45/2.00  --comb_res_mult                         3
% 11.45/2.00  --comb_sup_mult                         2
% 11.45/2.00  --comb_inst_mult                        10
% 11.45/2.00  
% 11.45/2.00  ------ Debug Options
% 11.45/2.00  
% 11.45/2.00  --dbg_backtrace                         false
% 11.45/2.00  --dbg_dump_prop_clauses                 false
% 11.45/2.00  --dbg_dump_prop_clauses_file            -
% 11.45/2.00  --dbg_out_stat                          false
% 11.45/2.00  
% 11.45/2.00  
% 11.45/2.00  
% 11.45/2.00  
% 11.45/2.00  ------ Proving...
% 11.45/2.00  
% 11.45/2.00  
% 11.45/2.00  % SZS status Theorem for theBenchmark.p
% 11.45/2.00  
% 11.45/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.45/2.00  
% 11.45/2.00  fof(f1,axiom,(
% 11.45/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.45/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/2.00  
% 11.45/2.00  fof(f19,plain,(
% 11.45/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.45/2.00    inference(ennf_transformation,[],[f1])).
% 11.45/2.00  
% 11.45/2.00  fof(f39,plain,(
% 11.45/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.45/2.00    inference(nnf_transformation,[],[f19])).
% 11.45/2.00  
% 11.45/2.00  fof(f40,plain,(
% 11.45/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.45/2.00    inference(rectify,[],[f39])).
% 11.45/2.00  
% 11.45/2.00  fof(f41,plain,(
% 11.45/2.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.45/2.00    introduced(choice_axiom,[])).
% 11.45/2.00  
% 11.45/2.00  fof(f42,plain,(
% 11.45/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.45/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 11.45/2.00  
% 11.45/2.00  fof(f58,plain,(
% 11.45/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.45/2.00    inference(cnf_transformation,[],[f42])).
% 11.45/2.00  
% 11.45/2.00  fof(f5,axiom,(
% 11.45/2.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.45/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/2.00  
% 11.45/2.00  fof(f20,plain,(
% 11.45/2.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.45/2.00    inference(ennf_transformation,[],[f5])).
% 11.45/2.00  
% 11.45/2.00  fof(f45,plain,(
% 11.45/2.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.45/2.00    inference(nnf_transformation,[],[f20])).
% 11.45/2.00  
% 11.45/2.00  fof(f66,plain,(
% 11.45/2.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 11.45/2.00    inference(cnf_transformation,[],[f45])).
% 11.45/2.00  
% 11.45/2.00  fof(f4,axiom,(
% 11.45/2.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.45/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/2.00  
% 11.45/2.00  fof(f64,plain,(
% 11.45/2.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.45/2.00    inference(cnf_transformation,[],[f4])).
% 11.45/2.00  
% 11.45/2.00  fof(f16,axiom,(
% 11.45/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 11.45/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/2.00  
% 11.45/2.00  fof(f35,plain,(
% 11.45/2.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 11.45/2.00    inference(ennf_transformation,[],[f16])).
% 11.45/2.00  
% 11.45/2.00  fof(f36,plain,(
% 11.45/2.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 11.45/2.00    inference(flattening,[],[f35])).
% 11.45/2.00  
% 11.45/2.00  fof(f50,plain,(
% 11.45/2.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 11.45/2.00    inference(nnf_transformation,[],[f36])).
% 11.45/2.00  
% 11.45/2.00  fof(f51,plain,(
% 11.45/2.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 11.45/2.00    inference(rectify,[],[f50])).
% 11.45/2.00  
% 11.45/2.00  fof(f53,plain,(
% 11.45/2.00    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 11.45/2.00    introduced(choice_axiom,[])).
% 11.45/2.00  
% 11.45/2.00  fof(f52,plain,(
% 11.45/2.00    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))))),
% 11.45/2.00    introduced(choice_axiom,[])).
% 11.45/2.00  
% 11.45/2.00  fof(f54,plain,(
% 11.45/2.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 11.45/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f51,f53,f52])).
% 11.45/2.00  
% 11.45/2.00  fof(f85,plain,(
% 11.45/2.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | r2_hidden(sK2(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 11.45/2.00    inference(cnf_transformation,[],[f54])).
% 11.45/2.00  
% 11.45/2.00  fof(f96,plain,(
% 11.45/2.00    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_orders_2(X1,X2)) | r2_hidden(sK2(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 11.45/2.00    inference(equality_resolution,[],[f85])).
% 11.45/2.00  
% 11.45/2.00  fof(f17,conjecture,(
% 11.45/2.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 11.45/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/2.00  
% 11.45/2.00  fof(f18,negated_conjecture,(
% 11.45/2.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 11.45/2.00    inference(negated_conjecture,[],[f17])).
% 11.45/2.00  
% 11.45/2.00  fof(f37,plain,(
% 11.45/2.00    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 11.45/2.00    inference(ennf_transformation,[],[f18])).
% 11.45/2.00  
% 11.45/2.00  fof(f38,plain,(
% 11.45/2.00    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.45/2.00    inference(flattening,[],[f37])).
% 11.45/2.00  
% 11.45/2.00  fof(f55,plain,(
% 11.45/2.00    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (u1_struct_0(sK4) != k2_orders_2(sK4,k1_struct_0(sK4)) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4))),
% 11.45/2.00    introduced(choice_axiom,[])).
% 11.45/2.00  
% 11.45/2.00  fof(f56,plain,(
% 11.45/2.00    u1_struct_0(sK4) != k2_orders_2(sK4,k1_struct_0(sK4)) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4)),
% 11.45/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f55])).
% 11.45/2.00  
% 11.45/2.00  fof(f90,plain,(
% 11.45/2.00    v5_orders_2(sK4)),
% 11.45/2.00    inference(cnf_transformation,[],[f56])).
% 11.45/2.00  
% 11.45/2.00  fof(f87,plain,(
% 11.45/2.00    ~v2_struct_0(sK4)),
% 11.45/2.00    inference(cnf_transformation,[],[f56])).
% 11.45/2.00  
% 11.45/2.00  fof(f88,plain,(
% 11.45/2.00    v3_orders_2(sK4)),
% 11.45/2.00    inference(cnf_transformation,[],[f56])).
% 11.45/2.00  
% 11.45/2.00  fof(f89,plain,(
% 11.45/2.00    v4_orders_2(sK4)),
% 11.45/2.00    inference(cnf_transformation,[],[f56])).
% 11.45/2.00  
% 11.45/2.00  fof(f91,plain,(
% 11.45/2.00    l1_orders_2(sK4)),
% 11.45/2.00    inference(cnf_transformation,[],[f56])).
% 11.45/2.00  
% 11.45/2.00  fof(f11,axiom,(
% 11.45/2.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 11.45/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/2.00  
% 11.45/2.00  fof(f28,plain,(
% 11.45/2.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 11.45/2.00    inference(ennf_transformation,[],[f11])).
% 11.45/2.00  
% 11.45/2.00  fof(f76,plain,(
% 11.45/2.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 11.45/2.00    inference(cnf_transformation,[],[f28])).
% 11.45/2.00  
% 11.45/2.00  fof(f6,axiom,(
% 11.45/2.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 11.45/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/2.00  
% 11.45/2.00  fof(f69,plain,(
% 11.45/2.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.45/2.00    inference(cnf_transformation,[],[f6])).
% 11.45/2.00  
% 11.45/2.00  fof(f13,axiom,(
% 11.45/2.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 11.45/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/2.00  
% 11.45/2.00  fof(f30,plain,(
% 11.45/2.00    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 11.45/2.00    inference(ennf_transformation,[],[f13])).
% 11.45/2.00  
% 11.45/2.00  fof(f31,plain,(
% 11.45/2.00    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 11.45/2.00    inference(flattening,[],[f30])).
% 11.45/2.00  
% 11.45/2.00  fof(f78,plain,(
% 11.45/2.00    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 11.45/2.00    inference(cnf_transformation,[],[f31])).
% 11.45/2.00  
% 11.45/2.00  fof(f59,plain,(
% 11.45/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.45/2.00    inference(cnf_transformation,[],[f42])).
% 11.45/2.00  
% 11.45/2.00  fof(f14,axiom,(
% 11.45/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.45/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/2.00  
% 11.45/2.00  fof(f32,plain,(
% 11.45/2.00    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 11.45/2.00    inference(ennf_transformation,[],[f14])).
% 11.45/2.00  
% 11.45/2.00  fof(f33,plain,(
% 11.45/2.00    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 11.45/2.00    inference(flattening,[],[f32])).
% 11.45/2.00  
% 11.45/2.00  fof(f79,plain,(
% 11.45/2.00    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 11.45/2.00    inference(cnf_transformation,[],[f33])).
% 11.45/2.00  
% 11.45/2.00  fof(f9,axiom,(
% 11.45/2.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 11.45/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/2.00  
% 11.45/2.00  fof(f25,plain,(
% 11.45/2.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 11.45/2.00    inference(ennf_transformation,[],[f9])).
% 11.45/2.00  
% 11.45/2.00  fof(f26,plain,(
% 11.45/2.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.45/2.00    inference(flattening,[],[f25])).
% 11.45/2.00  
% 11.45/2.00  fof(f74,plain,(
% 11.45/2.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.45/2.00    inference(cnf_transformation,[],[f26])).
% 11.45/2.00  
% 11.45/2.00  fof(f8,axiom,(
% 11.45/2.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 11.45/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/2.00  
% 11.45/2.00  fof(f23,plain,(
% 11.45/2.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 11.45/2.00    inference(ennf_transformation,[],[f8])).
% 11.45/2.00  
% 11.45/2.00  fof(f24,plain,(
% 11.45/2.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 11.45/2.00    inference(flattening,[],[f23])).
% 11.45/2.00  
% 11.45/2.00  fof(f73,plain,(
% 11.45/2.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 11.45/2.00    inference(cnf_transformation,[],[f24])).
% 11.45/2.00  
% 11.45/2.00  fof(f10,axiom,(
% 11.45/2.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 11.45/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/2.00  
% 11.45/2.00  fof(f27,plain,(
% 11.45/2.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.45/2.00    inference(ennf_transformation,[],[f10])).
% 11.45/2.00  
% 11.45/2.00  fof(f75,plain,(
% 11.45/2.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.45/2.00    inference(cnf_transformation,[],[f27])).
% 11.45/2.00  
% 11.45/2.00  fof(f68,plain,(
% 11.45/2.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 11.45/2.00    inference(cnf_transformation,[],[f45])).
% 11.45/2.00  
% 11.45/2.00  fof(f3,axiom,(
% 11.45/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.45/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/2.00  
% 11.45/2.00  fof(f43,plain,(
% 11.45/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.45/2.00    inference(nnf_transformation,[],[f3])).
% 11.45/2.00  
% 11.45/2.00  fof(f44,plain,(
% 11.45/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.45/2.00    inference(flattening,[],[f43])).
% 11.45/2.00  
% 11.45/2.00  fof(f63,plain,(
% 11.45/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.45/2.00    inference(cnf_transformation,[],[f44])).
% 11.45/2.00  
% 11.45/2.00  fof(f61,plain,(
% 11.45/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.45/2.00    inference(cnf_transformation,[],[f44])).
% 11.45/2.00  
% 11.45/2.00  fof(f94,plain,(
% 11.45/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.45/2.00    inference(equality_resolution,[],[f61])).
% 11.45/2.00  
% 11.45/2.00  fof(f12,axiom,(
% 11.45/2.00    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 11.45/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/2.00  
% 11.45/2.00  fof(f29,plain,(
% 11.45/2.00    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 11.45/2.00    inference(ennf_transformation,[],[f12])).
% 11.45/2.00  
% 11.45/2.00  fof(f77,plain,(
% 11.45/2.00    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 11.45/2.00    inference(cnf_transformation,[],[f29])).
% 11.45/2.00  
% 11.45/2.00  fof(f15,axiom,(
% 11.45/2.00    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 11.45/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/2.00  
% 11.45/2.00  fof(f34,plain,(
% 11.45/2.00    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 11.45/2.00    inference(ennf_transformation,[],[f15])).
% 11.45/2.00  
% 11.45/2.00  fof(f80,plain,(
% 11.45/2.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 11.45/2.00    inference(cnf_transformation,[],[f34])).
% 11.45/2.00  
% 11.45/2.00  fof(f92,plain,(
% 11.45/2.00    u1_struct_0(sK4) != k2_orders_2(sK4,k1_struct_0(sK4))),
% 11.45/2.00    inference(cnf_transformation,[],[f56])).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1,plain,
% 11.45/2.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.45/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1264,plain,
% 11.45/2.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.45/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.45/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_10,plain,
% 11.45/2.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.45/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1256,plain,
% 11.45/2.00      ( m1_subset_1(X0,X1) = iProver_top
% 11.45/2.00      | r2_hidden(X0,X1) != iProver_top
% 11.45/2.00      | v1_xboole_0(X1) = iProver_top ),
% 11.45/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_3292,plain,
% 11.45/2.00      ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
% 11.45/2.00      | r1_tarski(X0,X1) = iProver_top
% 11.45/2.00      | v1_xboole_0(X0) = iProver_top ),
% 11.45/2.00      inference(superposition,[status(thm)],[c_1264,c_1256]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_7,plain,
% 11.45/2.00      ( r1_tarski(k1_xboole_0,X0) ),
% 11.45/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1259,plain,
% 11.45/2.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.45/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_25,plain,
% 11.45/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.45/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.45/2.00      | r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 11.45/2.00      | r2_hidden(sK2(X1,X2,X0),X2)
% 11.45/2.00      | v2_struct_0(X1)
% 11.45/2.00      | ~ v3_orders_2(X1)
% 11.45/2.00      | ~ v4_orders_2(X1)
% 11.45/2.00      | ~ v5_orders_2(X1)
% 11.45/2.00      | ~ l1_orders_2(X1) ),
% 11.45/2.00      inference(cnf_transformation,[],[f96]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_32,negated_conjecture,
% 11.45/2.00      ( v5_orders_2(sK4) ),
% 11.45/2.00      inference(cnf_transformation,[],[f90]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_537,plain,
% 11.45/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.45/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.45/2.00      | r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 11.45/2.00      | r2_hidden(sK2(X1,X2,X0),X2)
% 11.45/2.00      | v2_struct_0(X1)
% 11.45/2.00      | ~ v3_orders_2(X1)
% 11.45/2.00      | ~ v4_orders_2(X1)
% 11.45/2.00      | ~ l1_orders_2(X1)
% 11.45/2.00      | sK4 != X1 ),
% 11.45/2.00      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_538,plain,
% 11.45/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 11.45/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.45/2.00      | r2_hidden(X0,a_2_1_orders_2(sK4,X1))
% 11.45/2.00      | r2_hidden(sK2(sK4,X1,X0),X1)
% 11.45/2.00      | v2_struct_0(sK4)
% 11.45/2.00      | ~ v3_orders_2(sK4)
% 11.45/2.00      | ~ v4_orders_2(sK4)
% 11.45/2.00      | ~ l1_orders_2(sK4) ),
% 11.45/2.00      inference(unflattening,[status(thm)],[c_537]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_35,negated_conjecture,
% 11.45/2.00      ( ~ v2_struct_0(sK4) ),
% 11.45/2.00      inference(cnf_transformation,[],[f87]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_34,negated_conjecture,
% 11.45/2.00      ( v3_orders_2(sK4) ),
% 11.45/2.00      inference(cnf_transformation,[],[f88]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_33,negated_conjecture,
% 11.45/2.00      ( v4_orders_2(sK4) ),
% 11.45/2.00      inference(cnf_transformation,[],[f89]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_31,negated_conjecture,
% 11.45/2.00      ( l1_orders_2(sK4) ),
% 11.45/2.00      inference(cnf_transformation,[],[f91]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_542,plain,
% 11.45/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 11.45/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.45/2.00      | r2_hidden(X0,a_2_1_orders_2(sK4,X1))
% 11.45/2.00      | r2_hidden(sK2(sK4,X1,X0),X1) ),
% 11.45/2.00      inference(global_propositional_subsumption,
% 11.45/2.00                [status(thm)],
% 11.45/2.00                [c_538,c_35,c_34,c_33,c_31]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1243,plain,
% 11.45/2.00      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.45/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.45/2.00      | r2_hidden(X0,a_2_1_orders_2(sK4,X1)) = iProver_top
% 11.45/2.00      | r2_hidden(sK2(sK4,X1,X0),X1) = iProver_top ),
% 11.45/2.00      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_19,plain,
% 11.45/2.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 11.45/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1248,plain,
% 11.45/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.45/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.45/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_2451,plain,
% 11.45/2.00      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.45/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.45/2.00      | r2_hidden(X0,a_2_1_orders_2(sK4,X1)) = iProver_top
% 11.45/2.00      | r1_tarski(X1,sK2(sK4,X1,X0)) != iProver_top ),
% 11.45/2.00      inference(superposition,[status(thm)],[c_1243,c_1248]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_2695,plain,
% 11.45/2.00      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.45/2.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.45/2.00      | r2_hidden(X0,a_2_1_orders_2(sK4,k1_xboole_0)) = iProver_top ),
% 11.45/2.00      inference(superposition,[status(thm)],[c_1259,c_2451]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_12,plain,
% 11.45/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.45/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1254,plain,
% 11.45/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.45/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_21,plain,
% 11.45/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.45/2.00      | v2_struct_0(X1)
% 11.45/2.00      | ~ v3_orders_2(X1)
% 11.45/2.00      | ~ v4_orders_2(X1)
% 11.45/2.00      | ~ v5_orders_2(X1)
% 11.45/2.00      | ~ l1_orders_2(X1)
% 11.45/2.00      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 11.45/2.00      inference(cnf_transformation,[],[f78]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_579,plain,
% 11.45/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.45/2.00      | v2_struct_0(X1)
% 11.45/2.00      | ~ v3_orders_2(X1)
% 11.45/2.00      | ~ v4_orders_2(X1)
% 11.45/2.00      | ~ l1_orders_2(X1)
% 11.45/2.00      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0)
% 11.45/2.00      | sK4 != X1 ),
% 11.45/2.00      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_580,plain,
% 11.45/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.45/2.00      | v2_struct_0(sK4)
% 11.45/2.00      | ~ v3_orders_2(sK4)
% 11.45/2.00      | ~ v4_orders_2(sK4)
% 11.45/2.00      | ~ l1_orders_2(sK4)
% 11.45/2.00      | a_2_1_orders_2(sK4,X0) = k2_orders_2(sK4,X0) ),
% 11.45/2.00      inference(unflattening,[status(thm)],[c_579]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_584,plain,
% 11.45/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.45/2.00      | a_2_1_orders_2(sK4,X0) = k2_orders_2(sK4,X0) ),
% 11.45/2.00      inference(global_propositional_subsumption,
% 11.45/2.00                [status(thm)],
% 11.45/2.00                [c_580,c_35,c_34,c_33,c_31]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1241,plain,
% 11.45/2.00      ( a_2_1_orders_2(sK4,X0) = k2_orders_2(sK4,X0)
% 11.45/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 11.45/2.00      inference(predicate_to_equality,[status(thm)],[c_584]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1863,plain,
% 11.45/2.00      ( a_2_1_orders_2(sK4,k1_xboole_0) = k2_orders_2(sK4,k1_xboole_0) ),
% 11.45/2.00      inference(superposition,[status(thm)],[c_1254,c_1241]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_2696,plain,
% 11.45/2.00      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.45/2.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.45/2.00      | r2_hidden(X0,k2_orders_2(sK4,k1_xboole_0)) = iProver_top ),
% 11.45/2.00      inference(light_normalisation,[status(thm)],[c_2695,c_1863]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1509,plain,
% 11.45/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 11.45/2.00      inference(instantiation,[status(thm)],[c_12]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1515,plain,
% 11.45/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 11.45/2.00      inference(predicate_to_equality,[status(thm)],[c_1509]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_22749,plain,
% 11.45/2.00      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.45/2.00      | r2_hidden(X0,k2_orders_2(sK4,k1_xboole_0)) = iProver_top ),
% 11.45/2.00      inference(global_propositional_subsumption,
% 11.45/2.00                [status(thm)],
% 11.45/2.00                [c_2696,c_1515]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_0,plain,
% 11.45/2.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.45/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1265,plain,
% 11.45/2.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 11.45/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.45/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_22757,plain,
% 11.45/2.00      ( m1_subset_1(sK0(X0,k2_orders_2(sK4,k1_xboole_0)),u1_struct_0(sK4)) != iProver_top
% 11.45/2.00      | r1_tarski(X0,k2_orders_2(sK4,k1_xboole_0)) = iProver_top ),
% 11.45/2.00      inference(superposition,[status(thm)],[c_22749,c_1265]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_22984,plain,
% 11.45/2.00      ( r1_tarski(u1_struct_0(sK4),k2_orders_2(sK4,k1_xboole_0)) = iProver_top
% 11.45/2.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 11.45/2.00      inference(superposition,[status(thm)],[c_3292,c_22757]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_22,plain,
% 11.45/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.45/2.00      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.45/2.00      | v2_struct_0(X1)
% 11.45/2.00      | ~ v3_orders_2(X1)
% 11.45/2.00      | ~ v4_orders_2(X1)
% 11.45/2.00      | ~ v5_orders_2(X1)
% 11.45/2.00      | ~ l1_orders_2(X1) ),
% 11.45/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_561,plain,
% 11.45/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.45/2.00      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.45/2.00      | v2_struct_0(X1)
% 11.45/2.00      | ~ v3_orders_2(X1)
% 11.45/2.00      | ~ v4_orders_2(X1)
% 11.45/2.00      | ~ l1_orders_2(X1)
% 11.45/2.00      | sK4 != X1 ),
% 11.45/2.00      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_562,plain,
% 11.45/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.45/2.00      | m1_subset_1(k2_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.45/2.00      | v2_struct_0(sK4)
% 11.45/2.00      | ~ v3_orders_2(sK4)
% 11.45/2.00      | ~ v4_orders_2(sK4)
% 11.45/2.00      | ~ l1_orders_2(sK4) ),
% 11.45/2.00      inference(unflattening,[status(thm)],[c_561]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_566,plain,
% 11.45/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.45/2.00      | m1_subset_1(k2_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 11.45/2.00      inference(global_propositional_subsumption,
% 11.45/2.00                [status(thm)],
% 11.45/2.00                [c_562,c_35,c_34,c_33,c_31]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1242,plain,
% 11.45/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.45/2.00      | m1_subset_1(k2_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 11.45/2.00      inference(predicate_to_equality,[status(thm)],[c_566]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_17,plain,
% 11.45/2.00      ( m1_subset_1(X0,X1)
% 11.45/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.45/2.00      | ~ r2_hidden(X0,X2) ),
% 11.45/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1250,plain,
% 11.45/2.00      ( m1_subset_1(X0,X1) = iProver_top
% 11.45/2.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 11.45/2.00      | r2_hidden(X0,X2) != iProver_top ),
% 11.45/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_4722,plain,
% 11.45/2.00      ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
% 11.45/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.45/2.00      | r2_hidden(X0,k2_orders_2(sK4,X1)) != iProver_top ),
% 11.45/2.00      inference(superposition,[status(thm)],[c_1242,c_1250]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_5161,plain,
% 11.45/2.00      ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
% 11.45/2.00      | r2_hidden(X0,k2_orders_2(sK4,k1_xboole_0)) != iProver_top ),
% 11.45/2.00      inference(superposition,[status(thm)],[c_1254,c_4722]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_9439,plain,
% 11.45/2.00      ( m1_subset_1(sK0(k2_orders_2(sK4,k1_xboole_0),X0),u1_struct_0(sK4)) = iProver_top
% 11.45/2.00      | r1_tarski(k2_orders_2(sK4,k1_xboole_0),X0) = iProver_top ),
% 11.45/2.00      inference(superposition,[status(thm)],[c_1264,c_5161]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_16,plain,
% 11.45/2.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.45/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1255,plain,
% 11.45/2.00      ( m1_subset_1(X0,X1) != iProver_top
% 11.45/2.00      | r2_hidden(X0,X1) = iProver_top
% 11.45/2.00      | v1_xboole_0(X1) = iProver_top ),
% 11.45/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_10090,plain,
% 11.45/2.00      ( r2_hidden(sK0(k2_orders_2(sK4,k1_xboole_0),X0),u1_struct_0(sK4)) = iProver_top
% 11.45/2.00      | r1_tarski(k2_orders_2(sK4,k1_xboole_0),X0) = iProver_top
% 11.45/2.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 11.45/2.00      inference(superposition,[status(thm)],[c_9439,c_1255]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_18,plain,
% 11.45/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.45/2.00      | ~ r2_hidden(X2,X0)
% 11.45/2.00      | ~ v1_xboole_0(X1) ),
% 11.45/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1249,plain,
% 11.45/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.45/2.00      | r2_hidden(X2,X0) != iProver_top
% 11.45/2.00      | v1_xboole_0(X1) != iProver_top ),
% 11.45/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_4640,plain,
% 11.45/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.45/2.00      | r2_hidden(X1,k2_orders_2(sK4,X0)) != iProver_top
% 11.45/2.00      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 11.45/2.00      inference(superposition,[status(thm)],[c_1242,c_1249]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_5115,plain,
% 11.45/2.00      ( r2_hidden(X0,k2_orders_2(sK4,k1_xboole_0)) != iProver_top
% 11.45/2.00      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 11.45/2.00      inference(superposition,[status(thm)],[c_1254,c_4640]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_8747,plain,
% 11.45/2.00      ( r1_tarski(k2_orders_2(sK4,k1_xboole_0),X0) = iProver_top
% 11.45/2.00      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 11.45/2.00      inference(superposition,[status(thm)],[c_1264,c_5115]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_12242,plain,
% 11.45/2.00      ( r1_tarski(k2_orders_2(sK4,k1_xboole_0),X0) = iProver_top
% 11.45/2.00      | r2_hidden(sK0(k2_orders_2(sK4,k1_xboole_0),X0),u1_struct_0(sK4)) = iProver_top ),
% 11.45/2.00      inference(global_propositional_subsumption,
% 11.45/2.00                [status(thm)],
% 11.45/2.00                [c_10090,c_8747]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_12243,plain,
% 11.45/2.00      ( r2_hidden(sK0(k2_orders_2(sK4,k1_xboole_0),X0),u1_struct_0(sK4)) = iProver_top
% 11.45/2.00      | r1_tarski(k2_orders_2(sK4,k1_xboole_0),X0) = iProver_top ),
% 11.45/2.00      inference(renaming,[status(thm)],[c_12242]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_12250,plain,
% 11.45/2.00      ( r1_tarski(k2_orders_2(sK4,k1_xboole_0),u1_struct_0(sK4)) = iProver_top ),
% 11.45/2.00      inference(superposition,[status(thm)],[c_12243,c_1265]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_22761,plain,
% 11.45/2.00      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.45/2.00      | r1_tarski(k2_orders_2(sK4,k1_xboole_0),X0) != iProver_top ),
% 11.45/2.00      inference(superposition,[status(thm)],[c_22749,c_1248]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_22909,plain,
% 11.45/2.00      ( m1_subset_1(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top ),
% 11.45/2.00      inference(superposition,[status(thm)],[c_12250,c_22761]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_8,plain,
% 11.45/2.00      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) ),
% 11.45/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_2382,plain,
% 11.45/2.00      ( m1_subset_1(X0,u1_struct_0(sK4))
% 11.45/2.00      | ~ v1_xboole_0(X0)
% 11.45/2.00      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 11.45/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_8587,plain,
% 11.45/2.00      ( m1_subset_1(u1_struct_0(sK4),u1_struct_0(sK4))
% 11.45/2.00      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 11.45/2.00      inference(instantiation,[status(thm)],[c_2382]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_8588,plain,
% 11.45/2.00      ( m1_subset_1(u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top
% 11.45/2.00      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 11.45/2.00      inference(predicate_to_equality,[status(thm)],[c_8587]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_811,plain,
% 11.45/2.00      ( X0 != X1 | X2 != X3 | k2_orders_2(X0,X2) = k2_orders_2(X1,X3) ),
% 11.45/2.00      theory(equality) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_2761,plain,
% 11.45/2.00      ( k2_orders_2(sK4,k1_struct_0(sK4)) = k2_orders_2(X0,X1)
% 11.45/2.00      | k1_struct_0(sK4) != X1
% 11.45/2.00      | sK4 != X0 ),
% 11.45/2.00      inference(instantiation,[status(thm)],[c_811]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_6645,plain,
% 11.45/2.00      ( k2_orders_2(sK4,k1_struct_0(sK4)) = k2_orders_2(X0,k1_xboole_0)
% 11.45/2.00      | k1_struct_0(sK4) != k1_xboole_0
% 11.45/2.00      | sK4 != X0 ),
% 11.45/2.00      inference(instantiation,[status(thm)],[c_2761]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_6646,plain,
% 11.45/2.00      ( k2_orders_2(sK4,k1_struct_0(sK4)) = k2_orders_2(sK4,k1_xboole_0)
% 11.45/2.00      | k1_struct_0(sK4) != k1_xboole_0
% 11.45/2.00      | sK4 != sK4 ),
% 11.45/2.00      inference(instantiation,[status(thm)],[c_6645]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_4,plain,
% 11.45/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.45/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1918,plain,
% 11.45/2.00      ( ~ r1_tarski(X0,k2_orders_2(sK4,k1_xboole_0))
% 11.45/2.00      | ~ r1_tarski(k2_orders_2(sK4,k1_xboole_0),X0)
% 11.45/2.00      | X0 = k2_orders_2(sK4,k1_xboole_0) ),
% 11.45/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_6524,plain,
% 11.45/2.00      ( ~ r1_tarski(k2_orders_2(sK4,k1_xboole_0),u1_struct_0(sK4))
% 11.45/2.00      | ~ r1_tarski(u1_struct_0(sK4),k2_orders_2(sK4,k1_xboole_0))
% 11.45/2.00      | u1_struct_0(sK4) = k2_orders_2(sK4,k1_xboole_0) ),
% 11.45/2.00      inference(instantiation,[status(thm)],[c_1918]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_6532,plain,
% 11.45/2.00      ( u1_struct_0(sK4) = k2_orders_2(sK4,k1_xboole_0)
% 11.45/2.00      | r1_tarski(k2_orders_2(sK4,k1_xboole_0),u1_struct_0(sK4)) != iProver_top
% 11.45/2.00      | r1_tarski(u1_struct_0(sK4),k2_orders_2(sK4,k1_xboole_0)) != iProver_top ),
% 11.45/2.00      inference(predicate_to_equality,[status(thm)],[c_6524]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_804,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_1472,plain,
% 11.45/2.00      ( k2_orders_2(sK4,k1_struct_0(sK4)) != X0
% 11.45/2.00      | u1_struct_0(sK4) != X0
% 11.45/2.00      | u1_struct_0(sK4) = k2_orders_2(sK4,k1_struct_0(sK4)) ),
% 11.45/2.00      inference(instantiation,[status(thm)],[c_804]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_5345,plain,
% 11.45/2.00      ( k2_orders_2(sK4,k1_struct_0(sK4)) != k2_orders_2(sK4,k1_xboole_0)
% 11.45/2.00      | u1_struct_0(sK4) = k2_orders_2(sK4,k1_struct_0(sK4))
% 11.45/2.00      | u1_struct_0(sK4) != k2_orders_2(sK4,k1_xboole_0) ),
% 11.45/2.00      inference(instantiation,[status(thm)],[c_1472]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_111,plain,
% 11.45/2.00      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 11.45/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_6,plain,
% 11.45/2.00      ( r1_tarski(X0,X0) ),
% 11.45/2.00      inference(cnf_transformation,[],[f94]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_107,plain,
% 11.45/2.00      ( r1_tarski(sK4,sK4) ),
% 11.45/2.00      inference(instantiation,[status(thm)],[c_6]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_20,plain,
% 11.45/2.00      ( ~ l1_struct_0(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 11.45/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_69,plain,
% 11.45/2.00      ( ~ l1_struct_0(sK4) | k1_struct_0(sK4) = k1_xboole_0 ),
% 11.45/2.00      inference(instantiation,[status(thm)],[c_20]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_23,plain,
% 11.45/2.00      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 11.45/2.00      inference(cnf_transformation,[],[f80]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_60,plain,
% 11.45/2.00      ( ~ l1_orders_2(sK4) | l1_struct_0(sK4) ),
% 11.45/2.00      inference(instantiation,[status(thm)],[c_23]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(c_30,negated_conjecture,
% 11.45/2.00      ( u1_struct_0(sK4) != k2_orders_2(sK4,k1_struct_0(sK4)) ),
% 11.45/2.00      inference(cnf_transformation,[],[f92]) ).
% 11.45/2.00  
% 11.45/2.00  cnf(contradiction,plain,
% 11.45/2.00      ( $false ),
% 11.45/2.00      inference(minisat,
% 11.45/2.00                [status(thm)],
% 11.45/2.00                [c_22984,c_22909,c_12250,c_8588,c_6646,c_6532,c_5345,
% 11.45/2.00                 c_111,c_107,c_69,c_60,c_30,c_31]) ).
% 11.45/2.00  
% 11.45/2.00  
% 11.45/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.45/2.00  
% 11.45/2.00  ------                               Statistics
% 11.45/2.00  
% 11.45/2.00  ------ General
% 11.45/2.00  
% 11.45/2.00  abstr_ref_over_cycles:                  0
% 11.45/2.00  abstr_ref_under_cycles:                 0
% 11.45/2.00  gc_basic_clause_elim:                   0
% 11.45/2.00  forced_gc_time:                         0
% 11.45/2.00  parsing_time:                           0.01
% 11.45/2.00  unif_index_cands_time:                  0.
% 11.45/2.00  unif_index_add_time:                    0.
% 11.45/2.00  orderings_time:                         0.
% 11.45/2.00  out_proof_time:                         0.01
% 11.45/2.00  total_time:                             1.382
% 11.45/2.00  num_of_symbols:                         53
% 11.45/2.00  num_of_terms:                           19135
% 11.45/2.00  
% 11.45/2.00  ------ Preprocessing
% 11.45/2.00  
% 11.45/2.00  num_of_splits:                          0
% 11.45/2.00  num_of_split_atoms:                     0
% 11.45/2.00  num_of_reused_defs:                     0
% 11.45/2.00  num_eq_ax_congr_red:                    36
% 11.45/2.00  num_of_sem_filtered_clauses:            1
% 11.45/2.00  num_of_subtypes:                        0
% 11.45/2.00  monotx_restored_types:                  0
% 11.45/2.00  sat_num_of_epr_types:                   0
% 11.45/2.00  sat_num_of_non_cyclic_types:            0
% 11.45/2.00  sat_guarded_non_collapsed_types:        0
% 11.45/2.00  num_pure_diseq_elim:                    0
% 11.45/2.00  simp_replaced_by:                       0
% 11.45/2.00  res_preprocessed:                       142
% 11.45/2.00  prep_upred:                             0
% 11.45/2.00  prep_unflattend:                        11
% 11.45/2.00  smt_new_axioms:                         0
% 11.45/2.00  pred_elim_cands:                        4
% 11.45/2.00  pred_elim:                              7
% 11.45/2.00  pred_elim_cl:                           7
% 11.45/2.00  pred_elim_cycles:                       9
% 11.45/2.00  merged_defs:                            0
% 11.45/2.00  merged_defs_ncl:                        0
% 11.45/2.00  bin_hyper_res:                          0
% 11.45/2.00  prep_cycles:                            4
% 11.45/2.00  pred_elim_time:                         0.01
% 11.45/2.00  splitting_time:                         0.
% 11.45/2.00  sem_filter_time:                        0.
% 11.45/2.00  monotx_time:                            0.
% 11.45/2.00  subtype_inf_time:                       0.
% 11.45/2.00  
% 11.45/2.00  ------ Problem properties
% 11.45/2.00  
% 11.45/2.00  clauses:                                27
% 11.45/2.00  conjectures:                            1
% 11.45/2.00  epr:                                    10
% 11.45/2.00  horn:                                   20
% 11.45/2.00  ground:                                 3
% 11.45/2.00  unary:                                  6
% 11.45/2.00  binary:                                 5
% 11.45/2.00  lits:                                   73
% 11.45/2.00  lits_eq:                                8
% 11.45/2.00  fd_pure:                                0
% 11.45/2.00  fd_pseudo:                              0
% 11.45/2.00  fd_cond:                                0
% 11.45/2.00  fd_pseudo_cond:                         4
% 11.45/2.00  ac_symbols:                             0
% 11.45/2.00  
% 11.45/2.00  ------ Propositional Solver
% 11.45/2.00  
% 11.45/2.00  prop_solver_calls:                      29
% 11.45/2.00  prop_fast_solver_calls:                 1455
% 11.45/2.00  smt_solver_calls:                       0
% 11.45/2.00  smt_fast_solver_calls:                  0
% 11.45/2.00  prop_num_of_clauses:                    8233
% 11.45/2.00  prop_preprocess_simplified:             14344
% 11.45/2.00  prop_fo_subsumed:                       41
% 11.45/2.00  prop_solver_time:                       0.
% 11.45/2.00  smt_solver_time:                        0.
% 11.45/2.00  smt_fast_solver_time:                   0.
% 11.45/2.00  prop_fast_solver_time:                  0.
% 11.45/2.00  prop_unsat_core_time:                   0.
% 11.45/2.00  
% 11.45/2.00  ------ QBF
% 11.45/2.00  
% 11.45/2.00  qbf_q_res:                              0
% 11.45/2.00  qbf_num_tautologies:                    0
% 11.45/2.00  qbf_prep_cycles:                        0
% 11.45/2.00  
% 11.45/2.00  ------ BMC1
% 11.45/2.00  
% 11.45/2.00  bmc1_current_bound:                     -1
% 11.45/2.00  bmc1_last_solved_bound:                 -1
% 11.45/2.00  bmc1_unsat_core_size:                   -1
% 11.45/2.00  bmc1_unsat_core_parents_size:           -1
% 11.45/2.00  bmc1_merge_next_fun:                    0
% 11.45/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.45/2.00  
% 11.45/2.00  ------ Instantiation
% 11.45/2.00  
% 11.45/2.00  inst_num_of_clauses:                    1846
% 11.45/2.00  inst_num_in_passive:                    722
% 11.45/2.00  inst_num_in_active:                     711
% 11.45/2.00  inst_num_in_unprocessed:                413
% 11.45/2.00  inst_num_of_loops:                      1030
% 11.45/2.00  inst_num_of_learning_restarts:          0
% 11.45/2.00  inst_num_moves_active_passive:          316
% 11.45/2.00  inst_lit_activity:                      0
% 11.45/2.00  inst_lit_activity_moves:                0
% 11.45/2.00  inst_num_tautologies:                   0
% 11.45/2.00  inst_num_prop_implied:                  0
% 11.45/2.00  inst_num_existing_simplified:           0
% 11.45/2.00  inst_num_eq_res_simplified:             0
% 11.45/2.00  inst_num_child_elim:                    0
% 11.45/2.00  inst_num_of_dismatching_blockings:      602
% 11.45/2.00  inst_num_of_non_proper_insts:           1598
% 11.45/2.00  inst_num_of_duplicates:                 0
% 11.45/2.00  inst_inst_num_from_inst_to_res:         0
% 11.45/2.00  inst_dismatching_checking_time:         0.
% 11.45/2.00  
% 11.45/2.00  ------ Resolution
% 11.45/2.00  
% 11.45/2.00  res_num_of_clauses:                     0
% 11.45/2.00  res_num_in_passive:                     0
% 11.45/2.00  res_num_in_active:                      0
% 11.45/2.00  res_num_of_loops:                       146
% 11.45/2.00  res_forward_subset_subsumed:            235
% 11.45/2.00  res_backward_subset_subsumed:           0
% 11.45/2.00  res_forward_subsumed:                   0
% 11.45/2.00  res_backward_subsumed:                  0
% 11.45/2.00  res_forward_subsumption_resolution:     2
% 11.45/2.00  res_backward_subsumption_resolution:    0
% 11.45/2.00  res_clause_to_clause_subsumption:       12801
% 11.45/2.00  res_orphan_elimination:                 0
% 11.45/2.00  res_tautology_del:                      89
% 11.45/2.00  res_num_eq_res_simplified:              0
% 11.45/2.00  res_num_sel_changes:                    0
% 11.45/2.00  res_moves_from_active_to_pass:          0
% 11.45/2.00  
% 11.45/2.00  ------ Superposition
% 11.45/2.00  
% 11.45/2.00  sup_time_total:                         0.
% 11.45/2.00  sup_time_generating:                    0.
% 11.45/2.00  sup_time_sim_full:                      0.
% 11.45/2.00  sup_time_sim_immed:                     0.
% 11.45/2.00  
% 11.45/2.00  sup_num_of_clauses:                     1029
% 11.45/2.00  sup_num_in_active:                      205
% 11.45/2.00  sup_num_in_passive:                     824
% 11.45/2.00  sup_num_of_loops:                       204
% 11.45/2.00  sup_fw_superposition:                   658
% 11.45/2.00  sup_bw_superposition:                   485
% 11.45/2.00  sup_immediate_simplified:               106
% 11.45/2.00  sup_given_eliminated:                   0
% 11.45/2.00  comparisons_done:                       0
% 11.45/2.00  comparisons_avoided:                    0
% 11.45/2.00  
% 11.45/2.00  ------ Simplifications
% 11.45/2.00  
% 11.45/2.00  
% 11.45/2.00  sim_fw_subset_subsumed:                 21
% 11.45/2.00  sim_bw_subset_subsumed:                 1
% 11.45/2.00  sim_fw_subsumed:                        49
% 11.45/2.00  sim_bw_subsumed:                        5
% 11.45/2.00  sim_fw_subsumption_res:                 2
% 11.45/2.00  sim_bw_subsumption_res:                 1
% 11.45/2.00  sim_tautology_del:                      18
% 11.45/2.00  sim_eq_tautology_del:                   11
% 11.45/2.00  sim_eq_res_simp:                        0
% 11.45/2.00  sim_fw_demodulated:                     0
% 11.45/2.00  sim_bw_demodulated:                     1
% 11.45/2.00  sim_light_normalised:                   34
% 11.45/2.00  sim_joinable_taut:                      0
% 11.45/2.00  sim_joinable_simp:                      0
% 11.45/2.00  sim_ac_normalised:                      0
% 11.45/2.00  sim_smt_subsumption:                    0
% 11.45/2.00  
%------------------------------------------------------------------------------
