%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:05 EST 2020

% Result     : Theorem 55.58s
% Output     : CNFRefutation 55.58s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 556 expanded)
%              Number of clauses        :   88 ( 162 expanded)
%              Number of leaves         :   25 ( 127 expanded)
%              Depth                    :   17
%              Number of atoms          :  686 (2911 expanded)
%              Number of equality atoms :  117 ( 495 expanded)
%              Maximal formula depth    :   15 (   6 average)
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

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
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

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f49,plain,
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

fof(f50,plain,
    ( k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4))
    & l1_orders_2(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f49])).

fof(f82,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f40])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f47,plain,(
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

fof(f46,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK2(X1,X2,X3),X3)
        & r2_hidden(sK2(X1,X2,X3),X2)
        & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f45,f47,f46])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4409,plain,
    ( ~ r2_hidden(sK1(X0),X1)
    | r2_hidden(sK1(X0),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_18347,plain,
    ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X0)
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_4409])).

cnf(c_104862,plain,
    ( ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_18347])).

cnf(c_1097,plain,
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
    inference(cnf_transformation,[],[f70])).

cnf(c_30,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_709,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_710,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_32,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_31,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_29,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_714,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_710,c_33,c_32,c_31,c_29])).

cnf(c_6162,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | ~ r2_hidden(X2,k1_orders_2(sK4,X0))
    | X1 != X2 ),
    inference(resolution,[status(thm)],[c_1097,c_714])).

cnf(c_14,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2863,plain,
    ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_14,c_28])).

cnf(c_7099,plain,
    ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,a_2_0_orders_2(sK4,k2_struct_0(sK4)))
    | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_6162,c_2863])).

cnf(c_1094,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7127,plain,
    ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_7099,c_1094])).

cnf(c_21,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_58,plain,
    ( ~ l1_orders_2(sK4)
    | l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_76,plain,
    ( ~ l1_struct_0(sK4)
    | u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_104,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_108,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1100,plain,
    ( X0 != X1
    | k2_struct_0(X0) = k2_struct_0(X1) ),
    theory(equality)).

cnf(c_1111,plain,
    ( k2_struct_0(sK4) = k2_struct_0(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1100])).

cnf(c_1101,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1112,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1872,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1972,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1872])).

cnf(c_1973,plain,
    ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1098,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2965,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_1095,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_2227,plain,
    ( X0 != X1
    | k2_struct_0(sK4) != X1
    | k2_struct_0(sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_3212,plain,
    ( X0 != k2_struct_0(sK4)
    | k2_struct_0(sK4) = X0
    | k2_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2227])).

cnf(c_5296,plain,
    ( u1_struct_0(sK4) != k2_struct_0(sK4)
    | k2_struct_0(sK4) = u1_struct_0(sK4)
    | k2_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3212])).

cnf(c_1099,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1867,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1099])).

cnf(c_2013,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1867])).

cnf(c_2534,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | k2_struct_0(sK4) != X0
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2013])).

cnf(c_7820,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | k2_struct_0(sK4) != u1_struct_0(sK4)
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2534])).

cnf(c_102689,plain,
    ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7127,c_29,c_58,c_76,c_104,c_108,c_1111,c_1112,c_1972,c_1973,c_2965,c_5296,c_7820])).

cnf(c_6152,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1097,c_1094])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_622,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3(X2,X1,X0) = X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_623,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | sK3(X1,sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | sK3(X1,sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_623,c_33,c_32,c_31,c_29])).

cnf(c_10226,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | r2_hidden(sK3(X1,sK4,X0),X2) ),
    inference(resolution,[status(thm)],[c_6152,c_627])).

cnf(c_17,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_766,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_767,plain,
    ( ~ r2_orders_2(sK4,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_766])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f75])).

cnf(c_548,plain,
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
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_549,plain,
    ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_553,plain,
    ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_549,c_33,c_32,c_31,c_29])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_569,plain,
    ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_553,c_10])).

cnf(c_2503,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
    inference(resolution,[status(thm)],[c_767,c_569])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_601,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_30])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_606,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_602,c_33,c_32,c_31,c_29])).

cnf(c_808,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,a_2_0_orders_2(sK4,X1))
    | X0 != X2
    | sK3(X3,sK4,X1) != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_569,c_767])).

cnf(c_809,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_808])).

cnf(c_2517,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2503,c_606,c_809])).

cnf(c_11641,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0)) ),
    inference(resolution,[status(thm)],[c_10226,c_2517])).

cnf(c_102820,plain,
    ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_102689,c_11641])).

cnf(c_1096,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_3096,plain,
    ( ~ r1_tarski(X0,k2_struct_0(sK4))
    | r1_tarski(X1,k2_struct_0(sK4))
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_1096])).

cnf(c_13694,plain,
    ( r1_tarski(X0,k2_struct_0(sK4))
    | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4))
    | X0 != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3096])).

cnf(c_43905,plain,
    ( r1_tarski(u1_struct_0(sK4),k2_struct_0(sK4))
    | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4))
    | u1_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_13694])).

cnf(c_13695,plain,
    ( r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_691,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_692,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_696,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_692,c_33,c_32,c_31,c_29])).

cnf(c_2135,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k1_orders_2(sK4,X0),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_9,c_696])).

cnf(c_2887,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,k1_orders_2(sK4,X0))
    | r2_hidden(X1,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_2,c_2135])).

cnf(c_3166,plain,
    ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_2887,c_2863])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_104862,c_102820,c_43905,c_13695,c_7820,c_5296,c_3166,c_2965,c_1973,c_1972,c_1112,c_1111,c_108,c_104,c_76,c_58,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:50:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 55.58/7.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.58/7.52  
% 55.58/7.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.58/7.52  
% 55.58/7.52  ------  iProver source info
% 55.58/7.52  
% 55.58/7.52  git: date: 2020-06-30 10:37:57 +0100
% 55.58/7.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.58/7.52  git: non_committed_changes: false
% 55.58/7.52  git: last_make_outside_of_git: false
% 55.58/7.52  
% 55.58/7.52  ------ 
% 55.58/7.52  ------ Parsing...
% 55.58/7.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.58/7.52  
% 55.58/7.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 55.58/7.52  
% 55.58/7.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.58/7.52  
% 55.58/7.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.58/7.52  ------ Proving...
% 55.58/7.52  ------ Problem Properties 
% 55.58/7.52  
% 55.58/7.52  
% 55.58/7.52  clauses                                 25
% 55.58/7.52  conjectures                             1
% 55.58/7.52  EPR                                     5
% 55.58/7.52  Horn                                    21
% 55.58/7.52  unary                                   5
% 55.58/7.52  binary                                  9
% 55.58/7.52  lits                                    60
% 55.58/7.52  lits eq                                 10
% 55.58/7.52  fd_pure                                 0
% 55.58/7.52  fd_pseudo                               0
% 55.58/7.52  fd_cond                                 3
% 55.58/7.52  fd_pseudo_cond                          1
% 55.58/7.52  AC symbols                              0
% 55.58/7.52  
% 55.58/7.52  ------ Input Options Time Limit: Unbounded
% 55.58/7.52  
% 55.58/7.52  
% 55.58/7.52  ------ 
% 55.58/7.52  Current options:
% 55.58/7.52  ------ 
% 55.58/7.52  
% 55.58/7.52  
% 55.58/7.52  
% 55.58/7.52  
% 55.58/7.52  ------ Proving...
% 55.58/7.52  
% 55.58/7.52  
% 55.58/7.52  % SZS status Theorem for theBenchmark.p
% 55.58/7.52  
% 55.58/7.52  % SZS output start CNFRefutation for theBenchmark.p
% 55.58/7.52  
% 55.58/7.52  fof(f1,axiom,(
% 55.58/7.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 55.58/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.58/7.52  
% 55.58/7.52  fof(f17,plain,(
% 55.58/7.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 55.58/7.52    inference(ennf_transformation,[],[f1])).
% 55.58/7.52  
% 55.58/7.52  fof(f33,plain,(
% 55.58/7.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 55.58/7.52    inference(nnf_transformation,[],[f17])).
% 55.58/7.52  
% 55.58/7.52  fof(f34,plain,(
% 55.58/7.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 55.58/7.52    inference(rectify,[],[f33])).
% 55.58/7.52  
% 55.58/7.52  fof(f35,plain,(
% 55.58/7.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 55.58/7.52    introduced(choice_axiom,[])).
% 55.58/7.52  
% 55.58/7.52  fof(f36,plain,(
% 55.58/7.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 55.58/7.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 55.58/7.52  
% 55.58/7.52  fof(f51,plain,(
% 55.58/7.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 55.58/7.52    inference(cnf_transformation,[],[f36])).
% 55.58/7.52  
% 55.58/7.52  fof(f11,axiom,(
% 55.58/7.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 55.58/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.58/7.52  
% 55.58/7.52  fof(f24,plain,(
% 55.58/7.52    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 55.58/7.52    inference(ennf_transformation,[],[f11])).
% 55.58/7.52  
% 55.58/7.52  fof(f25,plain,(
% 55.58/7.52    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 55.58/7.52    inference(flattening,[],[f24])).
% 55.58/7.52  
% 55.58/7.52  fof(f70,plain,(
% 55.58/7.52    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 55.58/7.52    inference(cnf_transformation,[],[f25])).
% 55.58/7.52  
% 55.58/7.52  fof(f15,conjecture,(
% 55.58/7.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 55.58/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.58/7.52  
% 55.58/7.52  fof(f16,negated_conjecture,(
% 55.58/7.52    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 55.58/7.52    inference(negated_conjecture,[],[f15])).
% 55.58/7.52  
% 55.58/7.52  fof(f31,plain,(
% 55.58/7.52    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 55.58/7.52    inference(ennf_transformation,[],[f16])).
% 55.58/7.52  
% 55.58/7.52  fof(f32,plain,(
% 55.58/7.52    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 55.58/7.52    inference(flattening,[],[f31])).
% 55.58/7.52  
% 55.58/7.52  fof(f49,plain,(
% 55.58/7.52    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4))),
% 55.58/7.52    introduced(choice_axiom,[])).
% 55.58/7.52  
% 55.58/7.52  fof(f50,plain,(
% 55.58/7.52    k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4)),
% 55.58/7.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f49])).
% 55.58/7.52  
% 55.58/7.52  fof(f82,plain,(
% 55.58/7.52    v5_orders_2(sK4)),
% 55.58/7.52    inference(cnf_transformation,[],[f50])).
% 55.58/7.52  
% 55.58/7.52  fof(f79,plain,(
% 55.58/7.52    ~v2_struct_0(sK4)),
% 55.58/7.52    inference(cnf_transformation,[],[f50])).
% 55.58/7.52  
% 55.58/7.52  fof(f80,plain,(
% 55.58/7.52    v3_orders_2(sK4)),
% 55.58/7.52    inference(cnf_transformation,[],[f50])).
% 55.58/7.52  
% 55.58/7.52  fof(f81,plain,(
% 55.58/7.52    v4_orders_2(sK4)),
% 55.58/7.52    inference(cnf_transformation,[],[f50])).
% 55.58/7.52  
% 55.58/7.52  fof(f83,plain,(
% 55.58/7.52    l1_orders_2(sK4)),
% 55.58/7.52    inference(cnf_transformation,[],[f50])).
% 55.58/7.52  
% 55.58/7.52  fof(f8,axiom,(
% 55.58/7.52    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 55.58/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.58/7.52  
% 55.58/7.52  fof(f21,plain,(
% 55.58/7.52    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 55.58/7.52    inference(ennf_transformation,[],[f8])).
% 55.58/7.52  
% 55.58/7.52  fof(f40,plain,(
% 55.58/7.52    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 55.58/7.52    introduced(choice_axiom,[])).
% 55.58/7.52  
% 55.58/7.52  fof(f41,plain,(
% 55.58/7.52    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 55.58/7.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f40])).
% 55.58/7.52  
% 55.58/7.52  fof(f63,plain,(
% 55.58/7.52    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 55.58/7.52    inference(cnf_transformation,[],[f41])).
% 55.58/7.52  
% 55.58/7.52  fof(f84,plain,(
% 55.58/7.52    k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4))),
% 55.58/7.52    inference(cnf_transformation,[],[f50])).
% 55.58/7.52  
% 55.58/7.52  fof(f13,axiom,(
% 55.58/7.52    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 55.58/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.58/7.52  
% 55.58/7.52  fof(f28,plain,(
% 55.58/7.52    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 55.58/7.52    inference(ennf_transformation,[],[f13])).
% 55.58/7.52  
% 55.58/7.52  fof(f72,plain,(
% 55.58/7.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 55.58/7.52    inference(cnf_transformation,[],[f28])).
% 55.58/7.52  
% 55.58/7.52  fof(f9,axiom,(
% 55.58/7.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 55.58/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.58/7.52  
% 55.58/7.52  fof(f22,plain,(
% 55.58/7.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 55.58/7.52    inference(ennf_transformation,[],[f9])).
% 55.58/7.52  
% 55.58/7.52  fof(f66,plain,(
% 55.58/7.52    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 55.58/7.52    inference(cnf_transformation,[],[f22])).
% 55.58/7.52  
% 55.58/7.52  fof(f2,axiom,(
% 55.58/7.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 55.58/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.58/7.52  
% 55.58/7.52  fof(f37,plain,(
% 55.58/7.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 55.58/7.52    inference(nnf_transformation,[],[f2])).
% 55.58/7.52  
% 55.58/7.52  fof(f38,plain,(
% 55.58/7.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 55.58/7.52    inference(flattening,[],[f37])).
% 55.58/7.52  
% 55.58/7.52  fof(f54,plain,(
% 55.58/7.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 55.58/7.52    inference(cnf_transformation,[],[f38])).
% 55.58/7.52  
% 55.58/7.52  fof(f86,plain,(
% 55.58/7.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 55.58/7.52    inference(equality_resolution,[],[f54])).
% 55.58/7.52  
% 55.58/7.52  fof(f56,plain,(
% 55.58/7.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 55.58/7.52    inference(cnf_transformation,[],[f38])).
% 55.58/7.52  
% 55.58/7.52  fof(f5,axiom,(
% 55.58/7.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 55.58/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.58/7.52  
% 55.58/7.52  fof(f39,plain,(
% 55.58/7.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 55.58/7.52    inference(nnf_transformation,[],[f5])).
% 55.58/7.52  
% 55.58/7.52  fof(f60,plain,(
% 55.58/7.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 55.58/7.52    inference(cnf_transformation,[],[f39])).
% 55.58/7.52  
% 55.58/7.52  fof(f14,axiom,(
% 55.58/7.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 55.58/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.58/7.52  
% 55.58/7.52  fof(f29,plain,(
% 55.58/7.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 55.58/7.52    inference(ennf_transformation,[],[f14])).
% 55.58/7.52  
% 55.58/7.52  fof(f30,plain,(
% 55.58/7.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 55.58/7.52    inference(flattening,[],[f29])).
% 55.58/7.52  
% 55.58/7.52  fof(f44,plain,(
% 55.58/7.52    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 55.58/7.52    inference(nnf_transformation,[],[f30])).
% 55.58/7.52  
% 55.58/7.52  fof(f45,plain,(
% 55.58/7.52    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 55.58/7.52    inference(rectify,[],[f44])).
% 55.58/7.52  
% 55.58/7.52  fof(f47,plain,(
% 55.58/7.52    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK3(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 55.58/7.52    introduced(choice_axiom,[])).
% 55.58/7.52  
% 55.58/7.52  fof(f46,plain,(
% 55.58/7.52    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK2(X1,X2,X3),X3) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))))),
% 55.58/7.52    introduced(choice_axiom,[])).
% 55.58/7.52  
% 55.58/7.52  fof(f48,plain,(
% 55.58/7.52    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK2(X1,X2,X3),X3) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK3(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 55.58/7.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f45,f47,f46])).
% 55.58/7.52  
% 55.58/7.52  fof(f74,plain,(
% 55.58/7.52    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 55.58/7.52    inference(cnf_transformation,[],[f48])).
% 55.58/7.52  
% 55.58/7.52  fof(f10,axiom,(
% 55.58/7.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 55.58/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.58/7.52  
% 55.58/7.52  fof(f23,plain,(
% 55.58/7.52    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 55.58/7.52    inference(ennf_transformation,[],[f10])).
% 55.58/7.52  
% 55.58/7.52  fof(f42,plain,(
% 55.58/7.52    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 55.58/7.52    inference(nnf_transformation,[],[f23])).
% 55.58/7.52  
% 55.58/7.52  fof(f43,plain,(
% 55.58/7.52    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 55.58/7.52    inference(flattening,[],[f42])).
% 55.58/7.52  
% 55.58/7.52  fof(f68,plain,(
% 55.58/7.52    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 55.58/7.52    inference(cnf_transformation,[],[f43])).
% 55.58/7.52  
% 55.58/7.52  fof(f87,plain,(
% 55.58/7.52    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 55.58/7.52    inference(equality_resolution,[],[f68])).
% 55.58/7.52  
% 55.58/7.52  fof(f75,plain,(
% 55.58/7.52    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK3(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 55.58/7.52    inference(cnf_transformation,[],[f48])).
% 55.58/7.52  
% 55.58/7.52  fof(f6,axiom,(
% 55.58/7.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 55.58/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.58/7.52  
% 55.58/7.52  fof(f18,plain,(
% 55.58/7.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 55.58/7.52    inference(ennf_transformation,[],[f6])).
% 55.58/7.52  
% 55.58/7.52  fof(f19,plain,(
% 55.58/7.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 55.58/7.52    inference(flattening,[],[f18])).
% 55.58/7.52  
% 55.58/7.52  fof(f61,plain,(
% 55.58/7.52    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 55.58/7.52    inference(cnf_transformation,[],[f19])).
% 55.58/7.52  
% 55.58/7.52  fof(f73,plain,(
% 55.58/7.52    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 55.58/7.52    inference(cnf_transformation,[],[f48])).
% 55.58/7.52  
% 55.58/7.52  fof(f59,plain,(
% 55.58/7.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 55.58/7.52    inference(cnf_transformation,[],[f39])).
% 55.58/7.52  
% 55.58/7.52  fof(f12,axiom,(
% 55.58/7.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 55.58/7.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.58/7.52  
% 55.58/7.52  fof(f26,plain,(
% 55.58/7.52    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 55.58/7.52    inference(ennf_transformation,[],[f12])).
% 55.58/7.52  
% 55.58/7.52  fof(f27,plain,(
% 55.58/7.52    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 55.58/7.52    inference(flattening,[],[f26])).
% 55.58/7.52  
% 55.58/7.52  fof(f71,plain,(
% 55.58/7.52    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 55.58/7.52    inference(cnf_transformation,[],[f27])).
% 55.58/7.52  
% 55.58/7.52  cnf(c_2,plain,
% 55.58/7.52      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 55.58/7.52      inference(cnf_transformation,[],[f51]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_4409,plain,
% 55.58/7.52      ( ~ r2_hidden(sK1(X0),X1)
% 55.58/7.52      | r2_hidden(sK1(X0),X2)
% 55.58/7.52      | ~ r1_tarski(X1,X2) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_2]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_18347,plain,
% 55.58/7.52      ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X0)
% 55.58/7.52      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
% 55.58/7.52      | ~ r1_tarski(u1_struct_0(sK4),X0) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_4409]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_104862,plain,
% 55.58/7.52      ( ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
% 55.58/7.52      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4))
% 55.58/7.52      | ~ r1_tarski(u1_struct_0(sK4),k2_struct_0(sK4)) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_18347]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_1097,plain,
% 55.58/7.52      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 55.58/7.52      theory(equality) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_19,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.58/7.52      | v2_struct_0(X1)
% 55.58/7.52      | ~ v3_orders_2(X1)
% 55.58/7.52      | ~ v4_orders_2(X1)
% 55.58/7.52      | ~ v5_orders_2(X1)
% 55.58/7.52      | ~ l1_orders_2(X1)
% 55.58/7.52      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 55.58/7.52      inference(cnf_transformation,[],[f70]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_30,negated_conjecture,
% 55.58/7.52      ( v5_orders_2(sK4) ),
% 55.58/7.52      inference(cnf_transformation,[],[f82]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_709,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.58/7.52      | v2_struct_0(X1)
% 55.58/7.52      | ~ v3_orders_2(X1)
% 55.58/7.52      | ~ v4_orders_2(X1)
% 55.58/7.52      | ~ l1_orders_2(X1)
% 55.58/7.52      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
% 55.58/7.52      | sK4 != X1 ),
% 55.58/7.52      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_710,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | v2_struct_0(sK4)
% 55.58/7.52      | ~ v3_orders_2(sK4)
% 55.58/7.52      | ~ v4_orders_2(sK4)
% 55.58/7.52      | ~ l1_orders_2(sK4)
% 55.58/7.52      | a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0) ),
% 55.58/7.52      inference(unflattening,[status(thm)],[c_709]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_33,negated_conjecture,
% 55.58/7.52      ( ~ v2_struct_0(sK4) ),
% 55.58/7.52      inference(cnf_transformation,[],[f79]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_32,negated_conjecture,
% 55.58/7.52      ( v3_orders_2(sK4) ),
% 55.58/7.52      inference(cnf_transformation,[],[f80]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_31,negated_conjecture,
% 55.58/7.52      ( v4_orders_2(sK4) ),
% 55.58/7.52      inference(cnf_transformation,[],[f81]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_29,negated_conjecture,
% 55.58/7.52      ( l1_orders_2(sK4) ),
% 55.58/7.52      inference(cnf_transformation,[],[f83]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_714,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0) ),
% 55.58/7.52      inference(global_propositional_subsumption,
% 55.58/7.52                [status(thm)],
% 55.58/7.52                [c_710,c_33,c_32,c_31,c_29]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_6162,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 55.58/7.52      | ~ r2_hidden(X2,k1_orders_2(sK4,X0))
% 55.58/7.52      | X1 != X2 ),
% 55.58/7.52      inference(resolution,[status(thm)],[c_1097,c_714]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_14,plain,
% 55.58/7.52      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 55.58/7.52      inference(cnf_transformation,[],[f63]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_28,negated_conjecture,
% 55.58/7.52      ( k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) ),
% 55.58/7.52      inference(cnf_transformation,[],[f84]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_2863,plain,
% 55.58/7.52      ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 55.58/7.52      inference(resolution,[status(thm)],[c_14,c_28]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_7099,plain,
% 55.58/7.52      ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | r2_hidden(X0,a_2_0_orders_2(sK4,k2_struct_0(sK4)))
% 55.58/7.52      | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 55.58/7.52      inference(resolution,[status(thm)],[c_6162,c_2863]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_1094,plain,( X0 = X0 ),theory(equality) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_7127,plain,
% 55.58/7.52      ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,k2_struct_0(sK4))) ),
% 55.58/7.52      inference(resolution,[status(thm)],[c_7099,c_1094]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_21,plain,
% 55.58/7.52      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 55.58/7.52      inference(cnf_transformation,[],[f72]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_58,plain,
% 55.58/7.52      ( ~ l1_orders_2(sK4) | l1_struct_0(sK4) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_21]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_15,plain,
% 55.58/7.52      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 55.58/7.52      inference(cnf_transformation,[],[f66]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_76,plain,
% 55.58/7.52      ( ~ l1_struct_0(sK4) | u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_15]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_5,plain,
% 55.58/7.52      ( r1_tarski(X0,X0) ),
% 55.58/7.52      inference(cnf_transformation,[],[f86]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_104,plain,
% 55.58/7.52      ( r1_tarski(sK4,sK4) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_5]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_3,plain,
% 55.58/7.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 55.58/7.52      inference(cnf_transformation,[],[f56]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_108,plain,
% 55.58/7.52      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_3]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_1100,plain,
% 55.58/7.52      ( X0 != X1 | k2_struct_0(X0) = k2_struct_0(X1) ),
% 55.58/7.52      theory(equality) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_1111,plain,
% 55.58/7.52      ( k2_struct_0(sK4) = k2_struct_0(sK4) | sK4 != sK4 ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_1100]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_1101,plain,
% 55.58/7.52      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 55.58/7.52      theory(equality) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_1112,plain,
% 55.58/7.52      ( u1_struct_0(sK4) = u1_struct_0(sK4) | sK4 != sK4 ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_1101]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_8,plain,
% 55.58/7.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 55.58/7.52      inference(cnf_transformation,[],[f60]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_1872,plain,
% 55.58/7.52      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_8]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_1972,plain,
% 55.58/7.52      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_1872]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_1973,plain,
% 55.58/7.52      ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_5]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_1098,plain,
% 55.58/7.52      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 55.58/7.52      theory(equality) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_2965,plain,
% 55.58/7.52      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 55.58/7.52      | k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_1098]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_1095,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_2227,plain,
% 55.58/7.52      ( X0 != X1 | k2_struct_0(sK4) != X1 | k2_struct_0(sK4) = X0 ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_1095]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_3212,plain,
% 55.58/7.52      ( X0 != k2_struct_0(sK4)
% 55.58/7.52      | k2_struct_0(sK4) = X0
% 55.58/7.52      | k2_struct_0(sK4) != k2_struct_0(sK4) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_2227]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_5296,plain,
% 55.58/7.52      ( u1_struct_0(sK4) != k2_struct_0(sK4)
% 55.58/7.52      | k2_struct_0(sK4) = u1_struct_0(sK4)
% 55.58/7.52      | k2_struct_0(sK4) != k2_struct_0(sK4) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_3212]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_1099,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 55.58/7.52      theory(equality) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_1867,plain,
% 55.58/7.52      ( m1_subset_1(X0,X1)
% 55.58/7.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 55.58/7.52      | X0 != X2
% 55.58/7.52      | X1 != k1_zfmisc_1(X3) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_1099]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_2013,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 55.58/7.52      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 55.58/7.52      | X2 != X0
% 55.58/7.52      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_1867]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_2534,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | k2_struct_0(sK4) != X0
% 55.58/7.52      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_2013]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_7820,plain,
% 55.58/7.52      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | k2_struct_0(sK4) != u1_struct_0(sK4)
% 55.58/7.52      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_2534]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_102689,plain,
% 55.58/7.52      ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,k2_struct_0(sK4))) ),
% 55.58/7.52      inference(global_propositional_subsumption,
% 55.58/7.52                [status(thm)],
% 55.58/7.52                [c_7127,c_29,c_58,c_76,c_104,c_108,c_1111,c_1112,c_1972,
% 55.58/7.52                 c_1973,c_2965,c_5296,c_7820]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_6152,plain,
% 55.58/7.52      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 55.58/7.52      inference(resolution,[status(thm)],[c_1097,c_1094]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_26,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.58/7.52      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 55.58/7.52      | v2_struct_0(X1)
% 55.58/7.52      | ~ v3_orders_2(X1)
% 55.58/7.52      | ~ v4_orders_2(X1)
% 55.58/7.52      | ~ v5_orders_2(X1)
% 55.58/7.52      | ~ l1_orders_2(X1)
% 55.58/7.52      | sK3(X2,X1,X0) = X2 ),
% 55.58/7.52      inference(cnf_transformation,[],[f74]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_622,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.58/7.52      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 55.58/7.52      | v2_struct_0(X1)
% 55.58/7.52      | ~ v3_orders_2(X1)
% 55.58/7.52      | ~ v4_orders_2(X1)
% 55.58/7.52      | ~ l1_orders_2(X1)
% 55.58/7.52      | sK3(X2,X1,X0) = X2
% 55.58/7.52      | sK4 != X1 ),
% 55.58/7.52      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_623,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 55.58/7.52      | v2_struct_0(sK4)
% 55.58/7.52      | ~ v3_orders_2(sK4)
% 55.58/7.52      | ~ v4_orders_2(sK4)
% 55.58/7.52      | ~ l1_orders_2(sK4)
% 55.58/7.52      | sK3(X1,sK4,X0) = X1 ),
% 55.58/7.52      inference(unflattening,[status(thm)],[c_622]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_627,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 55.58/7.52      | sK3(X1,sK4,X0) = X1 ),
% 55.58/7.52      inference(global_propositional_subsumption,
% 55.58/7.52                [status(thm)],
% 55.58/7.52                [c_623,c_33,c_32,c_31,c_29]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_10226,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | ~ r2_hidden(X1,X2)
% 55.58/7.52      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 55.58/7.52      | r2_hidden(sK3(X1,sK4,X0),X2) ),
% 55.58/7.52      inference(resolution,[status(thm)],[c_6152,c_627]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_17,plain,
% 55.58/7.52      ( ~ r2_orders_2(X0,X1,X1)
% 55.58/7.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 55.58/7.52      | ~ l1_orders_2(X0) ),
% 55.58/7.52      inference(cnf_transformation,[],[f87]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_766,plain,
% 55.58/7.52      ( ~ r2_orders_2(X0,X1,X1)
% 55.58/7.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 55.58/7.52      | sK4 != X0 ),
% 55.58/7.52      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_767,plain,
% 55.58/7.52      ( ~ r2_orders_2(sK4,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 55.58/7.52      inference(unflattening,[status(thm)],[c_766]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_25,plain,
% 55.58/7.52      ( r2_orders_2(X0,X1,sK3(X2,X0,X3))
% 55.58/7.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 55.58/7.52      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 55.58/7.52      | ~ r2_hidden(X1,X3)
% 55.58/7.52      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 55.58/7.52      | v2_struct_0(X0)
% 55.58/7.52      | ~ v3_orders_2(X0)
% 55.58/7.52      | ~ v4_orders_2(X0)
% 55.58/7.52      | ~ v5_orders_2(X0)
% 55.58/7.52      | ~ l1_orders_2(X0) ),
% 55.58/7.52      inference(cnf_transformation,[],[f75]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_548,plain,
% 55.58/7.52      ( r2_orders_2(X0,X1,sK3(X2,X0,X3))
% 55.58/7.52      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 55.58/7.52      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 55.58/7.52      | ~ r2_hidden(X1,X3)
% 55.58/7.52      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 55.58/7.52      | v2_struct_0(X0)
% 55.58/7.52      | ~ v3_orders_2(X0)
% 55.58/7.52      | ~ v4_orders_2(X0)
% 55.58/7.52      | ~ l1_orders_2(X0)
% 55.58/7.52      | sK4 != X0 ),
% 55.58/7.52      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_549,plain,
% 55.58/7.52      ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
% 55.58/7.52      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 55.58/7.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | ~ r2_hidden(X0,X2)
% 55.58/7.52      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2))
% 55.58/7.52      | v2_struct_0(sK4)
% 55.58/7.52      | ~ v3_orders_2(sK4)
% 55.58/7.52      | ~ v4_orders_2(sK4)
% 55.58/7.52      | ~ l1_orders_2(sK4) ),
% 55.58/7.52      inference(unflattening,[status(thm)],[c_548]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_553,plain,
% 55.58/7.52      ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
% 55.58/7.52      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 55.58/7.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | ~ r2_hidden(X0,X2)
% 55.58/7.52      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2)) ),
% 55.58/7.52      inference(global_propositional_subsumption,
% 55.58/7.52                [status(thm)],
% 55.58/7.52                [c_549,c_33,c_32,c_31,c_29]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_10,plain,
% 55.58/7.52      ( m1_subset_1(X0,X1)
% 55.58/7.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 55.58/7.52      | ~ r2_hidden(X0,X2) ),
% 55.58/7.52      inference(cnf_transformation,[],[f61]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_569,plain,
% 55.58/7.52      ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
% 55.58/7.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | ~ r2_hidden(X0,X2)
% 55.58/7.52      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2)) ),
% 55.58/7.52      inference(forward_subsumption_resolution,
% 55.58/7.52                [status(thm)],
% 55.58/7.52                [c_553,c_10]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_2503,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | ~ m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
% 55.58/7.52      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 55.58/7.52      | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
% 55.58/7.52      inference(resolution,[status(thm)],[c_767,c_569]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_27,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.58/7.52      | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
% 55.58/7.52      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 55.58/7.52      | v2_struct_0(X1)
% 55.58/7.52      | ~ v3_orders_2(X1)
% 55.58/7.52      | ~ v4_orders_2(X1)
% 55.58/7.52      | ~ v5_orders_2(X1)
% 55.58/7.52      | ~ l1_orders_2(X1) ),
% 55.58/7.52      inference(cnf_transformation,[],[f73]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_601,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.58/7.52      | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
% 55.58/7.52      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 55.58/7.52      | v2_struct_0(X1)
% 55.58/7.52      | ~ v3_orders_2(X1)
% 55.58/7.52      | ~ v4_orders_2(X1)
% 55.58/7.52      | ~ l1_orders_2(X1)
% 55.58/7.52      | sK4 != X1 ),
% 55.58/7.52      inference(resolution_lifted,[status(thm)],[c_27,c_30]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_602,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
% 55.58/7.52      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 55.58/7.52      | v2_struct_0(sK4)
% 55.58/7.52      | ~ v3_orders_2(sK4)
% 55.58/7.52      | ~ v4_orders_2(sK4)
% 55.58/7.52      | ~ l1_orders_2(sK4) ),
% 55.58/7.52      inference(unflattening,[status(thm)],[c_601]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_606,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
% 55.58/7.52      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0)) ),
% 55.58/7.52      inference(global_propositional_subsumption,
% 55.58/7.52                [status(thm)],
% 55.58/7.52                [c_602,c_33,c_32,c_31,c_29]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_808,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 55.58/7.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | ~ r2_hidden(X2,X1)
% 55.58/7.52      | ~ r2_hidden(X3,a_2_0_orders_2(sK4,X1))
% 55.58/7.52      | X0 != X2
% 55.58/7.52      | sK3(X3,sK4,X1) != X0
% 55.58/7.52      | sK4 != sK4 ),
% 55.58/7.52      inference(resolution_lifted,[status(thm)],[c_569,c_767]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_809,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | ~ m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
% 55.58/7.52      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 55.58/7.52      | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
% 55.58/7.52      inference(unflattening,[status(thm)],[c_808]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_2517,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 55.58/7.52      | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
% 55.58/7.52      inference(global_propositional_subsumption,
% 55.58/7.52                [status(thm)],
% 55.58/7.52                [c_2503,c_606,c_809]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_11641,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | ~ r2_hidden(X1,X0)
% 55.58/7.52      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0)) ),
% 55.58/7.52      inference(resolution,[status(thm)],[c_10226,c_2517]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_102820,plain,
% 55.58/7.52      ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) ),
% 55.58/7.52      inference(resolution,[status(thm)],[c_102689,c_11641]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_1096,plain,
% 55.58/7.52      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 55.58/7.52      theory(equality) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_3096,plain,
% 55.58/7.52      ( ~ r1_tarski(X0,k2_struct_0(sK4))
% 55.58/7.52      | r1_tarski(X1,k2_struct_0(sK4))
% 55.58/7.52      | X1 != X0 ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_1096]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_13694,plain,
% 55.58/7.52      ( r1_tarski(X0,k2_struct_0(sK4))
% 55.58/7.52      | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4))
% 55.58/7.52      | X0 != k2_struct_0(sK4) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_3096]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_43905,plain,
% 55.58/7.52      ( r1_tarski(u1_struct_0(sK4),k2_struct_0(sK4))
% 55.58/7.52      | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4))
% 55.58/7.52      | u1_struct_0(sK4) != k2_struct_0(sK4) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_13694]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_13695,plain,
% 55.58/7.52      ( r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4)) ),
% 55.58/7.52      inference(instantiation,[status(thm)],[c_5]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_9,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 55.58/7.52      inference(cnf_transformation,[],[f59]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_20,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.58/7.52      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 55.58/7.52      | v2_struct_0(X1)
% 55.58/7.52      | ~ v3_orders_2(X1)
% 55.58/7.52      | ~ v4_orders_2(X1)
% 55.58/7.52      | ~ v5_orders_2(X1)
% 55.58/7.52      | ~ l1_orders_2(X1) ),
% 55.58/7.52      inference(cnf_transformation,[],[f71]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_691,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.58/7.52      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 55.58/7.52      | v2_struct_0(X1)
% 55.58/7.52      | ~ v3_orders_2(X1)
% 55.58/7.52      | ~ v4_orders_2(X1)
% 55.58/7.52      | ~ l1_orders_2(X1)
% 55.58/7.52      | sK4 != X1 ),
% 55.58/7.52      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_692,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | v2_struct_0(sK4)
% 55.58/7.52      | ~ v3_orders_2(sK4)
% 55.58/7.52      | ~ v4_orders_2(sK4)
% 55.58/7.52      | ~ l1_orders_2(sK4) ),
% 55.58/7.52      inference(unflattening,[status(thm)],[c_691]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_696,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 55.58/7.52      inference(global_propositional_subsumption,
% 55.58/7.52                [status(thm)],
% 55.58/7.52                [c_692,c_33,c_32,c_31,c_29]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_2135,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | r1_tarski(k1_orders_2(sK4,X0),u1_struct_0(sK4)) ),
% 55.58/7.52      inference(resolution,[status(thm)],[c_9,c_696]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_2887,plain,
% 55.58/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | ~ r2_hidden(X1,k1_orders_2(sK4,X0))
% 55.58/7.52      | r2_hidden(X1,u1_struct_0(sK4)) ),
% 55.58/7.52      inference(resolution,[status(thm)],[c_2,c_2135]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(c_3166,plain,
% 55.58/7.52      ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 55.58/7.52      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4)) ),
% 55.58/7.52      inference(resolution,[status(thm)],[c_2887,c_2863]) ).
% 55.58/7.52  
% 55.58/7.52  cnf(contradiction,plain,
% 55.58/7.52      ( $false ),
% 55.58/7.52      inference(minisat,
% 55.58/7.52                [status(thm)],
% 55.58/7.52                [c_104862,c_102820,c_43905,c_13695,c_7820,c_5296,c_3166,
% 55.58/7.52                 c_2965,c_1973,c_1972,c_1112,c_1111,c_108,c_104,c_76,
% 55.58/7.52                 c_58,c_29]) ).
% 55.58/7.52  
% 55.58/7.52  
% 55.58/7.52  % SZS output end CNFRefutation for theBenchmark.p
% 55.58/7.52  
% 55.58/7.52  ------                               Statistics
% 55.58/7.52  
% 55.58/7.52  ------ Selected
% 55.58/7.52  
% 55.58/7.52  total_time:                             6.764
% 55.58/7.52  
%------------------------------------------------------------------------------
