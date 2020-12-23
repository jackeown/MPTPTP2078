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
% DateTime   : Thu Dec  3 12:12:05 EST 2020

% Result     : Theorem 35.51s
% Output     : CNFRefutation 35.51s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 704 expanded)
%              Number of clauses        :   94 ( 208 expanded)
%              Number of leaves         :   20 ( 155 expanded)
%              Depth                    :   17
%              Number of atoms          :  662 (3566 expanded)
%              Number of equality atoms :  130 ( 629 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f23,plain,(
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
    inference(flattening,[],[f23])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f30,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f46,plain,
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

fof(f47,plain,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f46])).

fof(f79,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
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

fof(f38,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f37])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f44,plain,(
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

fof(f43,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f42,f44,f43])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_1052,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_684,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_685,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_684])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_31,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_29,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_689,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_685,c_33,c_32,c_31,c_29])).

cnf(c_4347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | ~ r2_hidden(X2,k1_orders_2(sK3,X0))
    | X1 != X2 ),
    inference(resolution,[status(thm)],[c_1052,c_689])).

cnf(c_14,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2037,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_14,c_28])).

cnf(c_5143,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X0,a_2_0_orders_2(sK3,k2_struct_0(sK3)))
    | X0 != sK0(k1_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_4347,c_2037])).

cnf(c_1049,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5171,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_5143,c_1049])).

cnf(c_21,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_15,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_411,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_21,c_15])).

cnf(c_736,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_411,c_29])).

cnf(c_737,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_736])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1752,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1825,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1752])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1826,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2814,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_1050,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_2585,plain,
    ( X0 != X1
    | k2_struct_0(sK3) != X1
    | k2_struct_0(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_5753,plain,
    ( X0 != k2_struct_0(sK3)
    | k2_struct_0(sK3) = X0
    | k2_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2585])).

cnf(c_13506,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | k2_struct_0(sK3) = u1_struct_0(sK3)
    | k2_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_5753])).

cnf(c_1054,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1749,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_1886,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1749])).

cnf(c_2164,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_struct_0(sK3) != X0
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1886])).

cnf(c_16623,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0))
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_struct_0(sK3) != u1_struct_0(sK3)
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_2164])).

cnf(c_19463,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_struct_0(sK3) != u1_struct_0(sK3)
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_16623])).

cnf(c_1848,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_19464,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1848])).

cnf(c_72803,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5171,c_737,c_1825,c_1826,c_2814,c_13506,c_19463,c_19464])).

cnf(c_4339,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1052,c_1049])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_597,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X2,X1,X0) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_598,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | sK2(X1,sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | sK2(X1,sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_598,c_33,c_32,c_31,c_29])).

cnf(c_7222,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | r2_hidden(sK2(X1,sK3,X0),X2) ),
    inference(resolution,[status(thm)],[c_4339,c_602])).

cnf(c_17,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_741,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_742,plain,
    ( ~ r2_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_741])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f72])).

cnf(c_523,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_524,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_528,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_33,c_32,c_31,c_29])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_544,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_528,c_11])).

cnf(c_2290,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | ~ r2_hidden(sK2(X1,sK3,X0),X0) ),
    inference(resolution,[status(thm)],[c_742,c_544])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_576,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_30])).

cnf(c_577,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_581,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_577,c_33,c_32,c_31,c_29])).

cnf(c_783,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,a_2_0_orders_2(sK3,X1))
    | X0 != X2
    | sK2(X3,sK3,X1) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_544,c_742])).

cnf(c_784,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | ~ r2_hidden(sK2(X1,sK3,X0),X0) ),
    inference(unflattening,[status(thm)],[c_783])).

cnf(c_2304,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | ~ r2_hidden(sK2(X1,sK3,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2290,c_581,c_784])).

cnf(c_7981,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0)) ),
    inference(resolution,[status(thm)],[c_7222,c_2304])).

cnf(c_72891,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_72803,c_7981])).

cnf(c_1592,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1589,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1575,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_2068,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_1575])).

cnf(c_2609,plain,
    ( a_2_0_orders_2(sK3,u1_struct_0(sK3)) = k1_orders_2(sK3,u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1592,c_2068])).

cnf(c_2741,plain,
    ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_737,c_2609])).

cnf(c_2611,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | r1_tarski(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_2068])).

cnf(c_7194,plain,
    ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1592,c_2611])).

cnf(c_7782,plain,
    ( k1_orders_2(sK3,u1_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_2741,c_7194])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_666,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_667,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_666])).

cnf(c_671,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_667,c_33,c_32,c_31,c_29])).

cnf(c_1576,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1588,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2055,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k1_orders_2(sK3,X0),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1576,c_1588])).

cnf(c_2867,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k1_orders_2(sK3,X0),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_2055])).

cnf(c_24083,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7782,c_2867])).

cnf(c_24096,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k2_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_24083])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_236,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_237,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_236])).

cnf(c_306,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_237])).

cnf(c_1755,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),X0)
    | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
    | ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X0) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_9528,plain,
    ( ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3))
    | ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1755])).

cnf(c_1676,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
    | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_72891,c_24096,c_19464,c_19463,c_13506,c_9528,c_2814,c_1826,c_1825,c_1676,c_737,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:55:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 35.51/6.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.51/6.02  
% 35.51/6.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.51/6.02  
% 35.51/6.02  ------  iProver source info
% 35.51/6.02  
% 35.51/6.02  git: date: 2020-06-30 10:37:57 +0100
% 35.51/6.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.51/6.02  git: non_committed_changes: false
% 35.51/6.02  git: last_make_outside_of_git: false
% 35.51/6.02  
% 35.51/6.02  ------ 
% 35.51/6.02  ------ Parsing...
% 35.51/6.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.51/6.02  
% 35.51/6.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 35.51/6.02  
% 35.51/6.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.51/6.02  
% 35.51/6.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.51/6.02  ------ Proving...
% 35.51/6.02  ------ Problem Properties 
% 35.51/6.02  
% 35.51/6.02  
% 35.51/6.02  clauses                                 25
% 35.51/6.02  conjectures                             1
% 35.51/6.02  EPR                                     3
% 35.51/6.02  Horn                                    21
% 35.51/6.02  unary                                   7
% 35.51/6.02  binary                                  6
% 35.51/6.02  lits                                    59
% 35.51/6.02  lits eq                                 15
% 35.51/6.02  fd_pure                                 0
% 35.51/6.02  fd_pseudo                               0
% 35.51/6.02  fd_cond                                 4
% 35.51/6.02  fd_pseudo_cond                          1
% 35.51/6.02  AC symbols                              0
% 35.51/6.02  
% 35.51/6.02  ------ Input Options Time Limit: Unbounded
% 35.51/6.02  
% 35.51/6.02  
% 35.51/6.02  ------ 
% 35.51/6.02  Current options:
% 35.51/6.02  ------ 
% 35.51/6.02  
% 35.51/6.02  
% 35.51/6.02  
% 35.51/6.02  
% 35.51/6.02  ------ Proving...
% 35.51/6.02  
% 35.51/6.02  
% 35.51/6.02  % SZS status Theorem for theBenchmark.p
% 35.51/6.02  
% 35.51/6.02  % SZS output start CNFRefutation for theBenchmark.p
% 35.51/6.02  
% 35.51/6.02  fof(f11,axiom,(
% 35.51/6.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 35.51/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.51/6.02  
% 35.51/6.02  fof(f23,plain,(
% 35.51/6.02    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 35.51/6.02    inference(ennf_transformation,[],[f11])).
% 35.51/6.02  
% 35.51/6.02  fof(f24,plain,(
% 35.51/6.02    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 35.51/6.02    inference(flattening,[],[f23])).
% 35.51/6.02  
% 35.51/6.02  fof(f67,plain,(
% 35.51/6.02    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 35.51/6.02    inference(cnf_transformation,[],[f24])).
% 35.51/6.02  
% 35.51/6.02  fof(f15,conjecture,(
% 35.51/6.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 35.51/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.51/6.02  
% 35.51/6.02  fof(f16,negated_conjecture,(
% 35.51/6.02    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 35.51/6.02    inference(negated_conjecture,[],[f15])).
% 35.51/6.02  
% 35.51/6.02  fof(f30,plain,(
% 35.51/6.02    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 35.51/6.02    inference(ennf_transformation,[],[f16])).
% 35.51/6.02  
% 35.51/6.02  fof(f31,plain,(
% 35.51/6.02    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 35.51/6.02    inference(flattening,[],[f30])).
% 35.51/6.02  
% 35.51/6.02  fof(f46,plain,(
% 35.51/6.02    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 35.51/6.02    introduced(choice_axiom,[])).
% 35.51/6.02  
% 35.51/6.02  fof(f47,plain,(
% 35.51/6.02    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 35.51/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f46])).
% 35.51/6.02  
% 35.51/6.02  fof(f79,plain,(
% 35.51/6.02    v5_orders_2(sK3)),
% 35.51/6.02    inference(cnf_transformation,[],[f47])).
% 35.51/6.02  
% 35.51/6.02  fof(f76,plain,(
% 35.51/6.02    ~v2_struct_0(sK3)),
% 35.51/6.02    inference(cnf_transformation,[],[f47])).
% 35.51/6.02  
% 35.51/6.02  fof(f77,plain,(
% 35.51/6.02    v3_orders_2(sK3)),
% 35.51/6.02    inference(cnf_transformation,[],[f47])).
% 35.51/6.02  
% 35.51/6.02  fof(f78,plain,(
% 35.51/6.02    v4_orders_2(sK3)),
% 35.51/6.02    inference(cnf_transformation,[],[f47])).
% 35.51/6.02  
% 35.51/6.02  fof(f80,plain,(
% 35.51/6.02    l1_orders_2(sK3)),
% 35.51/6.02    inference(cnf_transformation,[],[f47])).
% 35.51/6.02  
% 35.51/6.02  fof(f8,axiom,(
% 35.51/6.02    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 35.51/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.51/6.02  
% 35.51/6.02  fof(f20,plain,(
% 35.51/6.02    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 35.51/6.02    inference(ennf_transformation,[],[f8])).
% 35.51/6.02  
% 35.51/6.02  fof(f37,plain,(
% 35.51/6.02    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 35.51/6.02    introduced(choice_axiom,[])).
% 35.51/6.02  
% 35.51/6.02  fof(f38,plain,(
% 35.51/6.02    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 35.51/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f37])).
% 35.51/6.02  
% 35.51/6.02  fof(f60,plain,(
% 35.51/6.02    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 35.51/6.02    inference(cnf_transformation,[],[f38])).
% 35.51/6.02  
% 35.51/6.02  fof(f81,plain,(
% 35.51/6.02    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))),
% 35.51/6.02    inference(cnf_transformation,[],[f47])).
% 35.51/6.02  
% 35.51/6.02  fof(f13,axiom,(
% 35.51/6.02    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 35.51/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.51/6.02  
% 35.51/6.02  fof(f27,plain,(
% 35.51/6.02    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 35.51/6.02    inference(ennf_transformation,[],[f13])).
% 35.51/6.02  
% 35.51/6.02  fof(f69,plain,(
% 35.51/6.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 35.51/6.02    inference(cnf_transformation,[],[f27])).
% 35.51/6.02  
% 35.51/6.02  fof(f9,axiom,(
% 35.51/6.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 35.51/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.51/6.02  
% 35.51/6.02  fof(f21,plain,(
% 35.51/6.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 35.51/6.02    inference(ennf_transformation,[],[f9])).
% 35.51/6.02  
% 35.51/6.02  fof(f63,plain,(
% 35.51/6.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 35.51/6.02    inference(cnf_transformation,[],[f21])).
% 35.51/6.02  
% 35.51/6.02  fof(f6,axiom,(
% 35.51/6.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 35.51/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.51/6.02  
% 35.51/6.02  fof(f36,plain,(
% 35.51/6.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 35.51/6.02    inference(nnf_transformation,[],[f6])).
% 35.51/6.02  
% 35.51/6.02  fof(f58,plain,(
% 35.51/6.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 35.51/6.02    inference(cnf_transformation,[],[f36])).
% 35.51/6.02  
% 35.51/6.02  fof(f1,axiom,(
% 35.51/6.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.51/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.51/6.02  
% 35.51/6.02  fof(f32,plain,(
% 35.51/6.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.51/6.02    inference(nnf_transformation,[],[f1])).
% 35.51/6.02  
% 35.51/6.02  fof(f33,plain,(
% 35.51/6.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.51/6.02    inference(flattening,[],[f32])).
% 35.51/6.02  
% 35.51/6.02  fof(f49,plain,(
% 35.51/6.02    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 35.51/6.02    inference(cnf_transformation,[],[f33])).
% 35.51/6.02  
% 35.51/6.02  fof(f82,plain,(
% 35.51/6.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.51/6.02    inference(equality_resolution,[],[f49])).
% 35.51/6.02  
% 35.51/6.02  fof(f14,axiom,(
% 35.51/6.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 35.51/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.51/6.02  
% 35.51/6.02  fof(f28,plain,(
% 35.51/6.02    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 35.51/6.02    inference(ennf_transformation,[],[f14])).
% 35.51/6.02  
% 35.51/6.02  fof(f29,plain,(
% 35.51/6.02    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 35.51/6.02    inference(flattening,[],[f28])).
% 35.51/6.02  
% 35.51/6.02  fof(f41,plain,(
% 35.51/6.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 35.51/6.02    inference(nnf_transformation,[],[f29])).
% 35.51/6.02  
% 35.51/6.02  fof(f42,plain,(
% 35.51/6.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 35.51/6.02    inference(rectify,[],[f41])).
% 35.51/6.02  
% 35.51/6.02  fof(f44,plain,(
% 35.51/6.02    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 35.51/6.02    introduced(choice_axiom,[])).
% 35.51/6.02  
% 35.51/6.02  fof(f43,plain,(
% 35.51/6.02    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 35.51/6.02    introduced(choice_axiom,[])).
% 35.51/6.02  
% 35.51/6.02  fof(f45,plain,(
% 35.51/6.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 35.51/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f42,f44,f43])).
% 35.51/6.02  
% 35.51/6.02  fof(f71,plain,(
% 35.51/6.02    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 35.51/6.02    inference(cnf_transformation,[],[f45])).
% 35.51/6.02  
% 35.51/6.02  fof(f10,axiom,(
% 35.51/6.02    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 35.51/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.51/6.02  
% 35.51/6.02  fof(f22,plain,(
% 35.51/6.02    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.51/6.02    inference(ennf_transformation,[],[f10])).
% 35.51/6.02  
% 35.51/6.02  fof(f39,plain,(
% 35.51/6.02    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.51/6.02    inference(nnf_transformation,[],[f22])).
% 35.51/6.02  
% 35.51/6.02  fof(f40,plain,(
% 35.51/6.02    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.51/6.02    inference(flattening,[],[f39])).
% 35.51/6.02  
% 35.51/6.02  fof(f65,plain,(
% 35.51/6.02    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.51/6.02    inference(cnf_transformation,[],[f40])).
% 35.51/6.02  
% 35.51/6.02  fof(f86,plain,(
% 35.51/6.02    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.51/6.02    inference(equality_resolution,[],[f65])).
% 35.51/6.02  
% 35.51/6.02  fof(f72,plain,(
% 35.51/6.02    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 35.51/6.02    inference(cnf_transformation,[],[f45])).
% 35.51/6.02  
% 35.51/6.02  fof(f7,axiom,(
% 35.51/6.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 35.51/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.51/6.02  
% 35.51/6.02  fof(f18,plain,(
% 35.51/6.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 35.51/6.02    inference(ennf_transformation,[],[f7])).
% 35.51/6.02  
% 35.51/6.02  fof(f19,plain,(
% 35.51/6.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 35.51/6.02    inference(flattening,[],[f18])).
% 35.51/6.02  
% 35.51/6.02  fof(f59,plain,(
% 35.51/6.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 35.51/6.02    inference(cnf_transformation,[],[f19])).
% 35.51/6.02  
% 35.51/6.02  fof(f70,plain,(
% 35.51/6.02    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 35.51/6.02    inference(cnf_transformation,[],[f45])).
% 35.51/6.02  
% 35.51/6.02  fof(f12,axiom,(
% 35.51/6.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 35.51/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.51/6.02  
% 35.51/6.02  fof(f25,plain,(
% 35.51/6.02    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 35.51/6.02    inference(ennf_transformation,[],[f12])).
% 35.51/6.02  
% 35.51/6.02  fof(f26,plain,(
% 35.51/6.02    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 35.51/6.02    inference(flattening,[],[f25])).
% 35.51/6.02  
% 35.51/6.02  fof(f68,plain,(
% 35.51/6.02    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 35.51/6.02    inference(cnf_transformation,[],[f26])).
% 35.51/6.02  
% 35.51/6.02  fof(f57,plain,(
% 35.51/6.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 35.51/6.02    inference(cnf_transformation,[],[f36])).
% 35.51/6.02  
% 35.51/6.02  fof(f4,axiom,(
% 35.51/6.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 35.51/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.51/6.02  
% 35.51/6.02  fof(f17,plain,(
% 35.51/6.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.51/6.02    inference(ennf_transformation,[],[f4])).
% 35.51/6.02  
% 35.51/6.02  fof(f55,plain,(
% 35.51/6.02    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.51/6.02    inference(cnf_transformation,[],[f17])).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1052,plain,
% 35.51/6.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.51/6.02      theory(equality) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_19,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.51/6.02      | v2_struct_0(X1)
% 35.51/6.02      | ~ v3_orders_2(X1)
% 35.51/6.02      | ~ v4_orders_2(X1)
% 35.51/6.02      | ~ v5_orders_2(X1)
% 35.51/6.02      | ~ l1_orders_2(X1)
% 35.51/6.02      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 35.51/6.02      inference(cnf_transformation,[],[f67]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_30,negated_conjecture,
% 35.51/6.02      ( v5_orders_2(sK3) ),
% 35.51/6.02      inference(cnf_transformation,[],[f79]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_684,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.51/6.02      | v2_struct_0(X1)
% 35.51/6.02      | ~ v3_orders_2(X1)
% 35.51/6.02      | ~ v4_orders_2(X1)
% 35.51/6.02      | ~ l1_orders_2(X1)
% 35.51/6.02      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
% 35.51/6.02      | sK3 != X1 ),
% 35.51/6.02      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_685,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | v2_struct_0(sK3)
% 35.51/6.02      | ~ v3_orders_2(sK3)
% 35.51/6.02      | ~ v4_orders_2(sK3)
% 35.51/6.02      | ~ l1_orders_2(sK3)
% 35.51/6.02      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 35.51/6.02      inference(unflattening,[status(thm)],[c_684]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_33,negated_conjecture,
% 35.51/6.02      ( ~ v2_struct_0(sK3) ),
% 35.51/6.02      inference(cnf_transformation,[],[f76]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_32,negated_conjecture,
% 35.51/6.02      ( v3_orders_2(sK3) ),
% 35.51/6.02      inference(cnf_transformation,[],[f77]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_31,negated_conjecture,
% 35.51/6.02      ( v4_orders_2(sK3) ),
% 35.51/6.02      inference(cnf_transformation,[],[f78]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_29,negated_conjecture,
% 35.51/6.02      ( l1_orders_2(sK3) ),
% 35.51/6.02      inference(cnf_transformation,[],[f80]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_689,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 35.51/6.02      inference(global_propositional_subsumption,
% 35.51/6.02                [status(thm)],
% 35.51/6.02                [c_685,c_33,c_32,c_31,c_29]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_4347,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 35.51/6.02      | ~ r2_hidden(X2,k1_orders_2(sK3,X0))
% 35.51/6.02      | X1 != X2 ),
% 35.51/6.02      inference(resolution,[status(thm)],[c_1052,c_689]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_14,plain,
% 35.51/6.02      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 35.51/6.02      inference(cnf_transformation,[],[f60]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_28,negated_conjecture,
% 35.51/6.02      ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 35.51/6.02      inference(cnf_transformation,[],[f81]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_2037,plain,
% 35.51/6.02      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) ),
% 35.51/6.02      inference(resolution,[status(thm)],[c_14,c_28]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_5143,plain,
% 35.51/6.02      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | r2_hidden(X0,a_2_0_orders_2(sK3,k2_struct_0(sK3)))
% 35.51/6.02      | X0 != sK0(k1_orders_2(sK3,k2_struct_0(sK3))) ),
% 35.51/6.02      inference(resolution,[status(thm)],[c_4347,c_2037]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1049,plain,( X0 = X0 ),theory(equality) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_5171,plain,
% 35.51/6.02      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) ),
% 35.51/6.02      inference(resolution,[status(thm)],[c_5143,c_1049]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_21,plain,
% 35.51/6.02      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 35.51/6.02      inference(cnf_transformation,[],[f69]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_15,plain,
% 35.51/6.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 35.51/6.02      inference(cnf_transformation,[],[f63]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_411,plain,
% 35.51/6.02      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 35.51/6.02      inference(resolution,[status(thm)],[c_21,c_15]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_736,plain,
% 35.51/6.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 35.51/6.02      inference(resolution_lifted,[status(thm)],[c_411,c_29]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_737,plain,
% 35.51/6.02      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 35.51/6.02      inference(unflattening,[status(thm)],[c_736]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_9,plain,
% 35.51/6.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.51/6.02      inference(cnf_transformation,[],[f58]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1752,plain,
% 35.51/6.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_9]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1825,plain,
% 35.51/6.02      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_1752]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1,plain,
% 35.51/6.02      ( r1_tarski(X0,X0) ),
% 35.51/6.02      inference(cnf_transformation,[],[f82]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1826,plain,
% 35.51/6.02      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_1]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_2814,plain,
% 35.51/6.02      ( k2_struct_0(sK3) = k2_struct_0(sK3) ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_1049]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1050,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_2585,plain,
% 35.51/6.02      ( X0 != X1 | k2_struct_0(sK3) != X1 | k2_struct_0(sK3) = X0 ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_1050]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_5753,plain,
% 35.51/6.02      ( X0 != k2_struct_0(sK3)
% 35.51/6.02      | k2_struct_0(sK3) = X0
% 35.51/6.02      | k2_struct_0(sK3) != k2_struct_0(sK3) ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_2585]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_13506,plain,
% 35.51/6.02      ( u1_struct_0(sK3) != k2_struct_0(sK3)
% 35.51/6.02      | k2_struct_0(sK3) = u1_struct_0(sK3)
% 35.51/6.02      | k2_struct_0(sK3) != k2_struct_0(sK3) ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_5753]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1054,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.51/6.02      theory(equality) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1749,plain,
% 35.51/6.02      ( m1_subset_1(X0,X1)
% 35.51/6.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 35.51/6.02      | X0 != X2
% 35.51/6.02      | X1 != k1_zfmisc_1(X3) ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_1054]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1886,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.51/6.02      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 35.51/6.02      | X2 != X0
% 35.51/6.02      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_1749]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_2164,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.51/6.02      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | k2_struct_0(sK3) != X0
% 35.51/6.02      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(X1) ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_1886]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_16623,plain,
% 35.51/6.02      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0))
% 35.51/6.02      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | k2_struct_0(sK3) != u1_struct_0(sK3)
% 35.51/6.02      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(X0) ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_2164]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_19463,plain,
% 35.51/6.02      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | k2_struct_0(sK3) != u1_struct_0(sK3)
% 35.51/6.02      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_16623]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1848,plain,
% 35.51/6.02      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_1049]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_19464,plain,
% 35.51/6.02      ( k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_1848]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_72803,plain,
% 35.51/6.02      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) ),
% 35.51/6.02      inference(global_propositional_subsumption,
% 35.51/6.02                [status(thm)],
% 35.51/6.02                [c_5171,c_737,c_1825,c_1826,c_2814,c_13506,c_19463,
% 35.51/6.02                 c_19464]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_4339,plain,
% 35.51/6.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 35.51/6.02      inference(resolution,[status(thm)],[c_1052,c_1049]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_26,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.51/6.02      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 35.51/6.02      | v2_struct_0(X1)
% 35.51/6.02      | ~ v3_orders_2(X1)
% 35.51/6.02      | ~ v4_orders_2(X1)
% 35.51/6.02      | ~ v5_orders_2(X1)
% 35.51/6.02      | ~ l1_orders_2(X1)
% 35.51/6.02      | sK2(X2,X1,X0) = X2 ),
% 35.51/6.02      inference(cnf_transformation,[],[f71]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_597,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.51/6.02      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 35.51/6.02      | v2_struct_0(X1)
% 35.51/6.02      | ~ v3_orders_2(X1)
% 35.51/6.02      | ~ v4_orders_2(X1)
% 35.51/6.02      | ~ l1_orders_2(X1)
% 35.51/6.02      | sK2(X2,X1,X0) = X2
% 35.51/6.02      | sK3 != X1 ),
% 35.51/6.02      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_598,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 35.51/6.02      | v2_struct_0(sK3)
% 35.51/6.02      | ~ v3_orders_2(sK3)
% 35.51/6.02      | ~ v4_orders_2(sK3)
% 35.51/6.02      | ~ l1_orders_2(sK3)
% 35.51/6.02      | sK2(X1,sK3,X0) = X1 ),
% 35.51/6.02      inference(unflattening,[status(thm)],[c_597]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_602,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 35.51/6.02      | sK2(X1,sK3,X0) = X1 ),
% 35.51/6.02      inference(global_propositional_subsumption,
% 35.51/6.02                [status(thm)],
% 35.51/6.02                [c_598,c_33,c_32,c_31,c_29]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_7222,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | ~ r2_hidden(X1,X2)
% 35.51/6.02      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 35.51/6.02      | r2_hidden(sK2(X1,sK3,X0),X2) ),
% 35.51/6.02      inference(resolution,[status(thm)],[c_4339,c_602]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_17,plain,
% 35.51/6.02      ( ~ r2_orders_2(X0,X1,X1)
% 35.51/6.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.51/6.02      | ~ l1_orders_2(X0) ),
% 35.51/6.02      inference(cnf_transformation,[],[f86]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_741,plain,
% 35.51/6.02      ( ~ r2_orders_2(X0,X1,X1)
% 35.51/6.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.51/6.02      | sK3 != X0 ),
% 35.51/6.02      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_742,plain,
% 35.51/6.02      ( ~ r2_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 35.51/6.02      inference(unflattening,[status(thm)],[c_741]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_25,plain,
% 35.51/6.02      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 35.51/6.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.51/6.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 35.51/6.02      | ~ r2_hidden(X1,X3)
% 35.51/6.02      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 35.51/6.02      | v2_struct_0(X0)
% 35.51/6.02      | ~ v3_orders_2(X0)
% 35.51/6.02      | ~ v4_orders_2(X0)
% 35.51/6.02      | ~ v5_orders_2(X0)
% 35.51/6.02      | ~ l1_orders_2(X0) ),
% 35.51/6.02      inference(cnf_transformation,[],[f72]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_523,plain,
% 35.51/6.02      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 35.51/6.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.51/6.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 35.51/6.02      | ~ r2_hidden(X1,X3)
% 35.51/6.02      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 35.51/6.02      | v2_struct_0(X0)
% 35.51/6.02      | ~ v3_orders_2(X0)
% 35.51/6.02      | ~ v4_orders_2(X0)
% 35.51/6.02      | ~ l1_orders_2(X0)
% 35.51/6.02      | sK3 != X0 ),
% 35.51/6.02      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_524,plain,
% 35.51/6.02      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 35.51/6.02      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 35.51/6.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | ~ r2_hidden(X0,X2)
% 35.51/6.02      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
% 35.51/6.02      | v2_struct_0(sK3)
% 35.51/6.02      | ~ v3_orders_2(sK3)
% 35.51/6.02      | ~ v4_orders_2(sK3)
% 35.51/6.02      | ~ l1_orders_2(sK3) ),
% 35.51/6.02      inference(unflattening,[status(thm)],[c_523]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_528,plain,
% 35.51/6.02      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 35.51/6.02      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 35.51/6.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | ~ r2_hidden(X0,X2)
% 35.51/6.02      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2)) ),
% 35.51/6.02      inference(global_propositional_subsumption,
% 35.51/6.02                [status(thm)],
% 35.51/6.02                [c_524,c_33,c_32,c_31,c_29]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_11,plain,
% 35.51/6.02      ( m1_subset_1(X0,X1)
% 35.51/6.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 35.51/6.02      | ~ r2_hidden(X0,X2) ),
% 35.51/6.02      inference(cnf_transformation,[],[f59]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_544,plain,
% 35.51/6.02      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 35.51/6.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | ~ r2_hidden(X0,X2)
% 35.51/6.02      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2)) ),
% 35.51/6.02      inference(forward_subsumption_resolution,
% 35.51/6.02                [status(thm)],
% 35.51/6.02                [c_528,c_11]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_2290,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | ~ m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 35.51/6.02      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 35.51/6.02      | ~ r2_hidden(sK2(X1,sK3,X0),X0) ),
% 35.51/6.02      inference(resolution,[status(thm)],[c_742,c_544]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_27,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.51/6.02      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 35.51/6.02      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 35.51/6.02      | v2_struct_0(X1)
% 35.51/6.02      | ~ v3_orders_2(X1)
% 35.51/6.02      | ~ v4_orders_2(X1)
% 35.51/6.02      | ~ v5_orders_2(X1)
% 35.51/6.02      | ~ l1_orders_2(X1) ),
% 35.51/6.02      inference(cnf_transformation,[],[f70]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_576,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.51/6.02      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 35.51/6.02      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 35.51/6.02      | v2_struct_0(X1)
% 35.51/6.02      | ~ v3_orders_2(X1)
% 35.51/6.02      | ~ v4_orders_2(X1)
% 35.51/6.02      | ~ l1_orders_2(X1)
% 35.51/6.02      | sK3 != X1 ),
% 35.51/6.02      inference(resolution_lifted,[status(thm)],[c_27,c_30]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_577,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 35.51/6.02      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 35.51/6.02      | v2_struct_0(sK3)
% 35.51/6.02      | ~ v3_orders_2(sK3)
% 35.51/6.02      | ~ v4_orders_2(sK3)
% 35.51/6.02      | ~ l1_orders_2(sK3) ),
% 35.51/6.02      inference(unflattening,[status(thm)],[c_576]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_581,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 35.51/6.02      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0)) ),
% 35.51/6.02      inference(global_propositional_subsumption,
% 35.51/6.02                [status(thm)],
% 35.51/6.02                [c_577,c_33,c_32,c_31,c_29]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_783,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 35.51/6.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | ~ r2_hidden(X2,X1)
% 35.51/6.02      | ~ r2_hidden(X3,a_2_0_orders_2(sK3,X1))
% 35.51/6.02      | X0 != X2
% 35.51/6.02      | sK2(X3,sK3,X1) != X0
% 35.51/6.02      | sK3 != sK3 ),
% 35.51/6.02      inference(resolution_lifted,[status(thm)],[c_544,c_742]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_784,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | ~ m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 35.51/6.02      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 35.51/6.02      | ~ r2_hidden(sK2(X1,sK3,X0),X0) ),
% 35.51/6.02      inference(unflattening,[status(thm)],[c_783]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_2304,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 35.51/6.02      | ~ r2_hidden(sK2(X1,sK3,X0),X0) ),
% 35.51/6.02      inference(global_propositional_subsumption,
% 35.51/6.02                [status(thm)],
% 35.51/6.02                [c_2290,c_581,c_784]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_7981,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | ~ r2_hidden(X1,X0)
% 35.51/6.02      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0)) ),
% 35.51/6.02      inference(resolution,[status(thm)],[c_7222,c_2304]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_72891,plain,
% 35.51/6.02      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) ),
% 35.51/6.02      inference(resolution,[status(thm)],[c_72803,c_7981]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1592,plain,
% 35.51/6.02      ( r1_tarski(X0,X0) = iProver_top ),
% 35.51/6.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1589,plain,
% 35.51/6.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 35.51/6.02      | r1_tarski(X0,X1) != iProver_top ),
% 35.51/6.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1575,plain,
% 35.51/6.02      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 35.51/6.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 35.51/6.02      inference(predicate_to_equality,[status(thm)],[c_689]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_2068,plain,
% 35.51/6.02      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 35.51/6.02      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
% 35.51/6.02      inference(superposition,[status(thm)],[c_1589,c_1575]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_2609,plain,
% 35.51/6.02      ( a_2_0_orders_2(sK3,u1_struct_0(sK3)) = k1_orders_2(sK3,u1_struct_0(sK3)) ),
% 35.51/6.02      inference(superposition,[status(thm)],[c_1592,c_2068]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_2741,plain,
% 35.51/6.02      ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,u1_struct_0(sK3)) ),
% 35.51/6.02      inference(superposition,[status(thm)],[c_737,c_2609]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_2611,plain,
% 35.51/6.02      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 35.51/6.02      | r1_tarski(X0,k2_struct_0(sK3)) != iProver_top ),
% 35.51/6.02      inference(superposition,[status(thm)],[c_737,c_2068]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_7194,plain,
% 35.51/6.02      ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 35.51/6.02      inference(superposition,[status(thm)],[c_1592,c_2611]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_7782,plain,
% 35.51/6.02      ( k1_orders_2(sK3,u1_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 35.51/6.02      inference(superposition,[status(thm)],[c_2741,c_7194]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_20,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.51/6.02      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 35.51/6.02      | v2_struct_0(X1)
% 35.51/6.02      | ~ v3_orders_2(X1)
% 35.51/6.02      | ~ v4_orders_2(X1)
% 35.51/6.02      | ~ v5_orders_2(X1)
% 35.51/6.02      | ~ l1_orders_2(X1) ),
% 35.51/6.02      inference(cnf_transformation,[],[f68]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_666,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.51/6.02      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 35.51/6.02      | v2_struct_0(X1)
% 35.51/6.02      | ~ v3_orders_2(X1)
% 35.51/6.02      | ~ v4_orders_2(X1)
% 35.51/6.02      | ~ l1_orders_2(X1)
% 35.51/6.02      | sK3 != X1 ),
% 35.51/6.02      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_667,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | v2_struct_0(sK3)
% 35.51/6.02      | ~ v3_orders_2(sK3)
% 35.51/6.02      | ~ v4_orders_2(sK3)
% 35.51/6.02      | ~ l1_orders_2(sK3) ),
% 35.51/6.02      inference(unflattening,[status(thm)],[c_666]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_671,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 35.51/6.02      inference(global_propositional_subsumption,
% 35.51/6.02                [status(thm)],
% 35.51/6.02                [c_667,c_33,c_32,c_31,c_29]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1576,plain,
% 35.51/6.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 35.51/6.02      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 35.51/6.02      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_10,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 35.51/6.02      inference(cnf_transformation,[],[f57]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1588,plain,
% 35.51/6.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.51/6.02      | r1_tarski(X0,X1) = iProver_top ),
% 35.51/6.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_2055,plain,
% 35.51/6.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 35.51/6.02      | r1_tarski(k1_orders_2(sK3,X0),u1_struct_0(sK3)) = iProver_top ),
% 35.51/6.02      inference(superposition,[status(thm)],[c_1576,c_1588]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_2867,plain,
% 35.51/6.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 35.51/6.02      | r1_tarski(k1_orders_2(sK3,X0),k2_struct_0(sK3)) = iProver_top ),
% 35.51/6.02      inference(superposition,[status(thm)],[c_737,c_2055]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_24083,plain,
% 35.51/6.02      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 35.51/6.02      | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k2_struct_0(sK3)) = iProver_top ),
% 35.51/6.02      inference(superposition,[status(thm)],[c_7782,c_2867]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_24096,plain,
% 35.51/6.02      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 35.51/6.02      | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k2_struct_0(sK3)) ),
% 35.51/6.02      inference(predicate_to_equality_rev,[status(thm)],[c_24083]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_7,plain,
% 35.51/6.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.51/6.02      | ~ r2_hidden(X2,X0)
% 35.51/6.02      | r2_hidden(X2,X1) ),
% 35.51/6.02      inference(cnf_transformation,[],[f55]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_236,plain,
% 35.51/6.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 35.51/6.02      inference(prop_impl,[status(thm)],[c_9]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_237,plain,
% 35.51/6.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.51/6.02      inference(renaming,[status(thm)],[c_236]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_306,plain,
% 35.51/6.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 35.51/6.02      inference(bin_hyper_res,[status(thm)],[c_7,c_237]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1755,plain,
% 35.51/6.02      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),X0)
% 35.51/6.02      | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
% 35.51/6.02      | ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X0) ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_306]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_9528,plain,
% 35.51/6.02      ( ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
% 35.51/6.02      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3))
% 35.51/6.02      | ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k2_struct_0(sK3)) ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_1755]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(c_1676,plain,
% 35.51/6.02      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
% 35.51/6.02      | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 35.51/6.02      inference(instantiation,[status(thm)],[c_14]) ).
% 35.51/6.02  
% 35.51/6.02  cnf(contradiction,plain,
% 35.51/6.02      ( $false ),
% 35.51/6.02      inference(minisat,
% 35.51/6.02                [status(thm)],
% 35.51/6.02                [c_72891,c_24096,c_19464,c_19463,c_13506,c_9528,c_2814,
% 35.51/6.02                 c_1826,c_1825,c_1676,c_737,c_28]) ).
% 35.51/6.02  
% 35.51/6.02  
% 35.51/6.02  % SZS output end CNFRefutation for theBenchmark.p
% 35.51/6.02  
% 35.51/6.02  ------                               Statistics
% 35.51/6.02  
% 35.51/6.02  ------ Selected
% 35.51/6.02  
% 35.51/6.02  total_time:                             5.353
% 35.51/6.02  
%------------------------------------------------------------------------------
