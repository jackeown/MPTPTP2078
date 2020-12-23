%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:06 EST 2020

% Result     : Theorem 11.60s
% Output     : CNFRefutation 11.60s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 966 expanded)
%              Number of clauses        :  125 ( 323 expanded)
%              Number of leaves         :   22 ( 212 expanded)
%              Depth                    :   22
%              Number of atoms          :  721 (4391 expanded)
%              Number of equality atoms :  196 ( 798 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,
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

fof(f38,plain,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f37])).

fof(f61,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f35,plain,(
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

fof(f34,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f35,f34])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f63,plain,(
    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_6799,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),X0),X1)
    | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),X0),k1_orders_2(sK3,k2_struct_0(sK3)))
    | ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_9614,plain,
    ( ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),X0),k1_orders_2(sK3,k2_struct_0(sK3)))
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),X0),k2_struct_0(sK3))
    | ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6799])).

cnf(c_26673,plain,
    ( ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k1_orders_2(sK3,k2_struct_0(sK3)))
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k2_struct_0(sK3))
    | ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_9614])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1617,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1618,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2216,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1617,c_1618])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1614,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_716,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_717,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_716])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_721,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_717,c_24,c_23,c_22,c_20])).

cnf(c_1605,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_12,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_337,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_12,c_6])).

cnf(c_769,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_337,c_20])).

cnf(c_770,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_769])).

cnf(c_1648,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1605,c_770])).

cnf(c_2122,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | r1_tarski(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1614,c_1648])).

cnf(c_2846,plain,
    ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_2216,c_2122])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X2,X1,X0) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_630,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | sK2(X1,sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_634,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | sK2(X1,sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_630,c_24,c_23,c_22,c_20])).

cnf(c_1609,plain,
    ( sK2(X0,sK3,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_1664,plain,
    ( sK2(X0,sK3,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1609,c_770])).

cnf(c_9250,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2846,c_1664])).

cnf(c_49,plain,
    ( ~ l1_orders_2(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_67,plain,
    ( ~ l1_struct_0(sK3)
    | u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1164,plain,
    ( X0 != X1
    | k2_struct_0(X0) = k2_struct_0(X1) ),
    theory(equality)).

cnf(c_1175,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1164])).

cnf(c_1165,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1176,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1165])).

cnf(c_1158,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1183,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1158])).

cnf(c_1903,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK3)),X0)
    | r1_tarski(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2621,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK3)),u1_struct_0(sK3))
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_2623,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2621])).

cnf(c_2622,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK3)),u1_struct_0(sK3))
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2625,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2622])).

cnf(c_1159,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_1992,plain,
    ( X0 != X1
    | k2_struct_0(sK3) != X1
    | k2_struct_0(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_2183,plain,
    ( X0 != k2_struct_0(sK3)
    | k2_struct_0(sK3) = X0
    | k2_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1992])).

cnf(c_2904,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | k2_struct_0(sK3) = u1_struct_0(sK3)
    | k2_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2183])).

cnf(c_1162,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_3648,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1162])).

cnf(c_1851,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3758,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1851])).

cnf(c_3759,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3758])).

cnf(c_1163,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1846,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1163])).

cnf(c_1935,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1846])).

cnf(c_2494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_struct_0(sK3) != X0
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1935])).

cnf(c_4566,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_struct_0(sK3) != u1_struct_0(sK3)
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2494])).

cnf(c_4567,plain,
    ( k2_struct_0(sK3) != u1_struct_0(sK3)
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4566])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1902,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7209,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1902])).

cnf(c_7216,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7209])).

cnf(c_4367,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3)))
    | ~ r1_tarski(X0,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7468,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3)))
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4367])).

cnf(c_7469,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7468])).

cnf(c_1160,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_3392,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_struct_0(sK3))
    | k2_struct_0(sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_1160])).

cnf(c_4445,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK3))
    | r1_tarski(X0,k2_struct_0(sK3))
    | k2_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3392])).

cnf(c_9230,plain,
    ( ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(sK3))
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3))
    | k2_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4445])).

cnf(c_9234,plain,
    ( k2_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9230])).

cnf(c_10067,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9250,c_20,c_49,c_67,c_1175,c_1176,c_1183,c_2623,c_2625,c_2904,c_3648,c_3759,c_4567,c_7216,c_7469,c_9234])).

cnf(c_10075,plain,
    ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),X0),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)),X0)
    | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1617,c_10067])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1615,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11288,plain,
    ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0)
    | k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10075,c_1615])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1922,plain,
    ( ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0)
    | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1841,plain,
    ( r2_hidden(sK0(X0,k1_xboole_0),X0)
    | r1_tarski(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1948,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k1_orders_2(sK3,k2_struct_0(sK3)))
    | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1841])).

cnf(c_2424,plain,
    ( sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1158])).

cnf(c_2310,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),a_2_0_orders_2(sK3,X0))
    | sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),sK3,X0) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_7205,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),a_2_0_orders_2(sK3,k2_struct_0(sK3)))
    | sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2310])).

cnf(c_1161,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2034,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k1_orders_2(sK3,k2_struct_0(sK3)))
    | X1 != k1_orders_2(sK3,k2_struct_0(sK3))
    | X0 != sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1161])).

cnf(c_2423,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),X0)
    | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k1_orders_2(sK3,k2_struct_0(sK3)))
    | X0 != k1_orders_2(sK3,k2_struct_0(sK3))
    | sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) != sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2034])).

cnf(c_7246,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),a_2_0_orders_2(sK3,k2_struct_0(sK3)))
    | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k1_orders_2(sK3,k2_struct_0(sK3)))
    | a_2_0_orders_2(sK3,k2_struct_0(sK3)) != k1_orders_2(sK3,k2_struct_0(sK3))
    | sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) != sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2423])).

cnf(c_11356,plain,
    ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11288,c_20,c_19,c_49,c_67,c_1175,c_1176,c_1183,c_1922,c_1948,c_2424,c_2621,c_2622,c_2846,c_2904,c_3648,c_3758,c_4566,c_7205,c_7246])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f54])).

cnf(c_557,plain,
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
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_558,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_562,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_558,c_24,c_23,c_22,c_20])).

cnf(c_1612,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_1705,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1612,c_770])).

cnf(c_8,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_774,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_775,plain,
    ( ~ r2_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_774])).

cnf(c_1604,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_775])).

cnf(c_1643,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1604,c_770])).

cnf(c_2225,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_1643])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_613,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_24,c_23,c_22,c_20])).

cnf(c_1610,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_1671,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1610,c_770])).

cnf(c_3277,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
    | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2225,c_1671])).

cnf(c_11363,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11356,c_3277])).

cnf(c_11389,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11363,c_2846])).

cnf(c_11421,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3)))
    | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k1_orders_2(sK3,k2_struct_0(sK3)))
    | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k2_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11389])).

cnf(c_2063,plain,
    ( ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X0)
    | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X1)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_1160])).

cnf(c_4065,plain,
    ( ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X0)
    | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k2_struct_0(sK3))
    | k2_struct_0(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_2063])).

cnf(c_7422,plain,
    ( ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),u1_struct_0(sK3))
    | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k2_struct_0(sK3))
    | k2_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4065])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_698,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_699,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_698])).

cnf(c_703,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_699,c_24,c_23,c_22,c_20])).

cnf(c_7204,plain,
    ( m1_subset_1(k1_orders_2(sK3,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_2069,plain,
    ( ~ m1_subset_1(k1_orders_2(sK3,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1902])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26673,c_11421,c_9230,c_7468,c_7422,c_7204,c_7209,c_4566,c_3758,c_3648,c_2904,c_2622,c_2621,c_2069,c_1948,c_1922,c_1183,c_1176,c_1175,c_67,c_49,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:51:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.60/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.60/1.98  
% 11.60/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.60/1.98  
% 11.60/1.98  ------  iProver source info
% 11.60/1.98  
% 11.60/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.60/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.60/1.98  git: non_committed_changes: false
% 11.60/1.98  git: last_make_outside_of_git: false
% 11.60/1.98  
% 11.60/1.98  ------ 
% 11.60/1.98  ------ Parsing...
% 11.60/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.60/1.98  
% 11.60/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 11.60/1.98  
% 11.60/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.60/1.98  
% 11.60/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.60/1.98  ------ Proving...
% 11.60/1.98  ------ Problem Properties 
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  clauses                                 17
% 11.60/1.98  conjectures                             1
% 11.60/1.98  EPR                                     2
% 11.60/1.98  Horn                                    14
% 11.60/1.98  unary                                   2
% 11.60/1.98  binary                                  8
% 11.60/1.98  lits                                    44
% 11.60/1.98  lits eq                                 5
% 11.60/1.98  fd_pure                                 0
% 11.60/1.98  fd_pseudo                               0
% 11.60/1.98  fd_cond                                 1
% 11.60/1.98  fd_pseudo_cond                          0
% 11.60/1.98  AC symbols                              0
% 11.60/1.98  
% 11.60/1.98  ------ Input Options Time Limit: Unbounded
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  ------ 
% 11.60/1.98  Current options:
% 11.60/1.98  ------ 
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  ------ Proving...
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  % SZS status Theorem for theBenchmark.p
% 11.60/1.98  
% 11.60/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.60/1.98  
% 11.60/1.98  fof(f1,axiom,(
% 11.60/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f12,plain,(
% 11.60/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.60/1.98    inference(ennf_transformation,[],[f1])).
% 11.60/1.98  
% 11.60/1.98  fof(f25,plain,(
% 11.60/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.60/1.98    inference(nnf_transformation,[],[f12])).
% 11.60/1.98  
% 11.60/1.98  fof(f26,plain,(
% 11.60/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.60/1.98    inference(rectify,[],[f25])).
% 11.60/1.98  
% 11.60/1.98  fof(f27,plain,(
% 11.60/1.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.60/1.98    introduced(choice_axiom,[])).
% 11.60/1.98  
% 11.60/1.98  fof(f28,plain,(
% 11.60/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.60/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 11.60/1.98  
% 11.60/1.98  fof(f39,plain,(
% 11.60/1.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f28])).
% 11.60/1.98  
% 11.60/1.98  fof(f40,plain,(
% 11.60/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f28])).
% 11.60/1.98  
% 11.60/1.98  fof(f41,plain,(
% 11.60/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f28])).
% 11.60/1.98  
% 11.60/1.98  fof(f3,axiom,(
% 11.60/1.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f29,plain,(
% 11.60/1.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.60/1.98    inference(nnf_transformation,[],[f3])).
% 11.60/1.98  
% 11.60/1.98  fof(f44,plain,(
% 11.60/1.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f29])).
% 11.60/1.98  
% 11.60/1.98  fof(f6,axiom,(
% 11.60/1.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f16,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 11.60/1.98    inference(ennf_transformation,[],[f6])).
% 11.60/1.98  
% 11.60/1.98  fof(f17,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 11.60/1.98    inference(flattening,[],[f16])).
% 11.60/1.98  
% 11.60/1.98  fof(f49,plain,(
% 11.60/1.98    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f17])).
% 11.60/1.98  
% 11.60/1.98  fof(f10,conjecture,(
% 11.60/1.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f11,negated_conjecture,(
% 11.60/1.98    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 11.60/1.98    inference(negated_conjecture,[],[f10])).
% 11.60/1.98  
% 11.60/1.98  fof(f23,plain,(
% 11.60/1.98    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 11.60/1.98    inference(ennf_transformation,[],[f11])).
% 11.60/1.98  
% 11.60/1.98  fof(f24,plain,(
% 11.60/1.98    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 11.60/1.98    inference(flattening,[],[f23])).
% 11.60/1.98  
% 11.60/1.98  fof(f37,plain,(
% 11.60/1.98    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 11.60/1.98    introduced(choice_axiom,[])).
% 11.60/1.98  
% 11.60/1.98  fof(f38,plain,(
% 11.60/1.98    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 11.60/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f37])).
% 11.60/1.98  
% 11.60/1.98  fof(f61,plain,(
% 11.60/1.98    v5_orders_2(sK3)),
% 11.60/1.98    inference(cnf_transformation,[],[f38])).
% 11.60/1.98  
% 11.60/1.98  fof(f58,plain,(
% 11.60/1.98    ~v2_struct_0(sK3)),
% 11.60/1.98    inference(cnf_transformation,[],[f38])).
% 11.60/1.98  
% 11.60/1.98  fof(f59,plain,(
% 11.60/1.98    v3_orders_2(sK3)),
% 11.60/1.98    inference(cnf_transformation,[],[f38])).
% 11.60/1.98  
% 11.60/1.98  fof(f60,plain,(
% 11.60/1.98    v4_orders_2(sK3)),
% 11.60/1.98    inference(cnf_transformation,[],[f38])).
% 11.60/1.98  
% 11.60/1.98  fof(f62,plain,(
% 11.60/1.98    l1_orders_2(sK3)),
% 11.60/1.98    inference(cnf_transformation,[],[f38])).
% 11.60/1.98  
% 11.60/1.98  fof(f8,axiom,(
% 11.60/1.98    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f20,plain,(
% 11.60/1.98    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 11.60/1.98    inference(ennf_transformation,[],[f8])).
% 11.60/1.98  
% 11.60/1.98  fof(f51,plain,(
% 11.60/1.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f20])).
% 11.60/1.98  
% 11.60/1.98  fof(f4,axiom,(
% 11.60/1.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f14,plain,(
% 11.60/1.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 11.60/1.98    inference(ennf_transformation,[],[f4])).
% 11.60/1.98  
% 11.60/1.98  fof(f45,plain,(
% 11.60/1.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f14])).
% 11.60/1.98  
% 11.60/1.98  fof(f9,axiom,(
% 11.60/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f21,plain,(
% 11.60/1.98    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 11.60/1.98    inference(ennf_transformation,[],[f9])).
% 11.60/1.98  
% 11.60/1.98  fof(f22,plain,(
% 11.60/1.98    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 11.60/1.98    inference(flattening,[],[f21])).
% 11.60/1.98  
% 11.60/1.98  fof(f32,plain,(
% 11.60/1.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 11.60/1.98    inference(nnf_transformation,[],[f22])).
% 11.60/1.98  
% 11.60/1.98  fof(f33,plain,(
% 11.60/1.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 11.60/1.98    inference(rectify,[],[f32])).
% 11.60/1.98  
% 11.60/1.98  fof(f35,plain,(
% 11.60/1.98    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 11.60/1.98    introduced(choice_axiom,[])).
% 11.60/1.98  
% 11.60/1.98  fof(f34,plain,(
% 11.60/1.98    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 11.60/1.98    introduced(choice_axiom,[])).
% 11.60/1.98  
% 11.60/1.98  fof(f36,plain,(
% 11.60/1.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 11.60/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f35,f34])).
% 11.60/1.98  
% 11.60/1.98  fof(f53,plain,(
% 11.60/1.98    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f36])).
% 11.60/1.98  
% 11.60/1.98  fof(f43,plain,(
% 11.60/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.60/1.98    inference(cnf_transformation,[],[f29])).
% 11.60/1.98  
% 11.60/1.98  fof(f2,axiom,(
% 11.60/1.98    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f13,plain,(
% 11.60/1.98    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 11.60/1.98    inference(ennf_transformation,[],[f2])).
% 11.60/1.98  
% 11.60/1.98  fof(f42,plain,(
% 11.60/1.98    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f13])).
% 11.60/1.98  
% 11.60/1.98  fof(f63,plain,(
% 11.60/1.98    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))),
% 11.60/1.98    inference(cnf_transformation,[],[f38])).
% 11.60/1.98  
% 11.60/1.98  fof(f54,plain,(
% 11.60/1.98    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f36])).
% 11.60/1.98  
% 11.60/1.98  fof(f5,axiom,(
% 11.60/1.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f15,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.60/1.98    inference(ennf_transformation,[],[f5])).
% 11.60/1.98  
% 11.60/1.98  fof(f30,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.60/1.98    inference(nnf_transformation,[],[f15])).
% 11.60/1.98  
% 11.60/1.98  fof(f31,plain,(
% 11.60/1.98    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 11.60/1.98    inference(flattening,[],[f30])).
% 11.60/1.98  
% 11.60/1.98  fof(f47,plain,(
% 11.60/1.98    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f31])).
% 11.60/1.98  
% 11.60/1.98  fof(f64,plain,(
% 11.60/1.98    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 11.60/1.98    inference(equality_resolution,[],[f47])).
% 11.60/1.98  
% 11.60/1.98  fof(f52,plain,(
% 11.60/1.98    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f36])).
% 11.60/1.98  
% 11.60/1.98  fof(f7,axiom,(
% 11.60/1.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.60/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.98  
% 11.60/1.98  fof(f18,plain,(
% 11.60/1.98    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 11.60/1.98    inference(ennf_transformation,[],[f7])).
% 11.60/1.98  
% 11.60/1.98  fof(f19,plain,(
% 11.60/1.98    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 11.60/1.98    inference(flattening,[],[f18])).
% 11.60/1.98  
% 11.60/1.98  fof(f50,plain,(
% 11.60/1.98    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 11.60/1.98    inference(cnf_transformation,[],[f19])).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2,plain,
% 11.60/1.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.60/1.98      inference(cnf_transformation,[],[f39]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_6799,plain,
% 11.60/1.98      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),X0),X1)
% 11.60/1.98      | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),X0),k1_orders_2(sK3,k2_struct_0(sK3)))
% 11.60/1.98      | ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X1) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_2]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_9614,plain,
% 11.60/1.98      ( ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),X0),k1_orders_2(sK3,k2_struct_0(sK3)))
% 11.60/1.98      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),X0),k2_struct_0(sK3))
% 11.60/1.98      | ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k2_struct_0(sK3)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_6799]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_26673,plain,
% 11.60/1.98      ( ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k1_orders_2(sK3,k2_struct_0(sK3)))
% 11.60/1.98      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k2_struct_0(sK3))
% 11.60/1.98      | ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k2_struct_0(sK3)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_9614]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1,plain,
% 11.60/1.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.60/1.98      inference(cnf_transformation,[],[f40]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1617,plain,
% 11.60/1.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.60/1.98      | r1_tarski(X0,X1) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_0,plain,
% 11.60/1.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.60/1.98      inference(cnf_transformation,[],[f41]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1618,plain,
% 11.60/1.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 11.60/1.98      | r1_tarski(X0,X1) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2216,plain,
% 11.60/1.98      ( r1_tarski(X0,X0) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1617,c_1618]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4,plain,
% 11.60/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.60/1.98      inference(cnf_transformation,[],[f44]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1614,plain,
% 11.60/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.60/1.98      | r1_tarski(X0,X1) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_10,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | v2_struct_0(X1)
% 11.60/1.98      | ~ v3_orders_2(X1)
% 11.60/1.98      | ~ v4_orders_2(X1)
% 11.60/1.98      | ~ v5_orders_2(X1)
% 11.60/1.98      | ~ l1_orders_2(X1)
% 11.60/1.98      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f49]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_21,negated_conjecture,
% 11.60/1.98      ( v5_orders_2(sK3) ),
% 11.60/1.98      inference(cnf_transformation,[],[f61]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_716,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | v2_struct_0(X1)
% 11.60/1.98      | ~ v3_orders_2(X1)
% 11.60/1.98      | ~ v4_orders_2(X1)
% 11.60/1.98      | ~ l1_orders_2(X1)
% 11.60/1.98      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
% 11.60/1.98      | sK3 != X1 ),
% 11.60/1.98      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_717,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | v2_struct_0(sK3)
% 11.60/1.98      | ~ v3_orders_2(sK3)
% 11.60/1.98      | ~ v4_orders_2(sK3)
% 11.60/1.98      | ~ l1_orders_2(sK3)
% 11.60/1.98      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 11.60/1.98      inference(unflattening,[status(thm)],[c_716]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_24,negated_conjecture,
% 11.60/1.98      ( ~ v2_struct_0(sK3) ),
% 11.60/1.98      inference(cnf_transformation,[],[f58]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_23,negated_conjecture,
% 11.60/1.98      ( v3_orders_2(sK3) ),
% 11.60/1.98      inference(cnf_transformation,[],[f59]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_22,negated_conjecture,
% 11.60/1.98      ( v4_orders_2(sK3) ),
% 11.60/1.98      inference(cnf_transformation,[],[f60]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_20,negated_conjecture,
% 11.60/1.98      ( l1_orders_2(sK3) ),
% 11.60/1.98      inference(cnf_transformation,[],[f62]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_721,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_717,c_24,c_23,c_22,c_20]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1605,plain,
% 11.60/1.98      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 11.60/1.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_721]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_12,plain,
% 11.60/1.98      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f51]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_6,plain,
% 11.60/1.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f45]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_337,plain,
% 11.60/1.98      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.60/1.98      inference(resolution,[status(thm)],[c_12,c_6]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_769,plain,
% 11.60/1.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 11.60/1.98      inference(resolution_lifted,[status(thm)],[c_337,c_20]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_770,plain,
% 11.60/1.98      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 11.60/1.98      inference(unflattening,[status(thm)],[c_769]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1648,plain,
% 11.60/1.98      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 11.60/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_1605,c_770]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2122,plain,
% 11.60/1.98      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 11.60/1.98      | r1_tarski(X0,k2_struct_0(sK3)) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1614,c_1648]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2846,plain,
% 11.60/1.98      ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_2216,c_2122]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_17,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 11.60/1.98      | v2_struct_0(X1)
% 11.60/1.98      | ~ v3_orders_2(X1)
% 11.60/1.98      | ~ v4_orders_2(X1)
% 11.60/1.98      | ~ v5_orders_2(X1)
% 11.60/1.98      | ~ l1_orders_2(X1)
% 11.60/1.98      | sK2(X2,X1,X0) = X2 ),
% 11.60/1.98      inference(cnf_transformation,[],[f53]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_629,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 11.60/1.98      | v2_struct_0(X1)
% 11.60/1.98      | ~ v3_orders_2(X1)
% 11.60/1.98      | ~ v4_orders_2(X1)
% 11.60/1.98      | ~ l1_orders_2(X1)
% 11.60/1.98      | sK2(X2,X1,X0) = X2
% 11.60/1.98      | sK3 != X1 ),
% 11.60/1.98      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_630,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 11.60/1.98      | v2_struct_0(sK3)
% 11.60/1.98      | ~ v3_orders_2(sK3)
% 11.60/1.98      | ~ v4_orders_2(sK3)
% 11.60/1.98      | ~ l1_orders_2(sK3)
% 11.60/1.98      | sK2(X1,sK3,X0) = X1 ),
% 11.60/1.98      inference(unflattening,[status(thm)],[c_629]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_634,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 11.60/1.98      | sK2(X1,sK3,X0) = X1 ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_630,c_24,c_23,c_22,c_20]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1609,plain,
% 11.60/1.98      ( sK2(X0,sK3,X1) = X0
% 11.60/1.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.60/1.98      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1664,plain,
% 11.60/1.98      ( sK2(X0,sK3,X1) = X0
% 11.60/1.98      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.60/1.98      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_1609,c_770]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_9250,plain,
% 11.60/1.98      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 11.60/1.98      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.60/1.98      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_2846,c_1664]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_49,plain,
% 11.60/1.98      ( ~ l1_orders_2(sK3) | l1_struct_0(sK3) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_12]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_67,plain,
% 11.60/1.98      ( ~ l1_struct_0(sK3) | u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_6]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1164,plain,
% 11.60/1.98      ( X0 != X1 | k2_struct_0(X0) = k2_struct_0(X1) ),
% 11.60/1.98      theory(equality) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1175,plain,
% 11.60/1.98      ( k2_struct_0(sK3) = k2_struct_0(sK3) | sK3 != sK3 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1164]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1165,plain,
% 11.60/1.98      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 11.60/1.98      theory(equality) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1176,plain,
% 11.60/1.98      ( u1_struct_0(sK3) = u1_struct_0(sK3) | sK3 != sK3 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1165]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1158,plain,( X0 = X0 ),theory(equality) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1183,plain,
% 11.60/1.98      ( sK3 = sK3 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1158]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1903,plain,
% 11.60/1.98      ( r2_hidden(sK0(X0,u1_struct_0(sK3)),X0)
% 11.60/1.98      | r1_tarski(X0,u1_struct_0(sK3)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2621,plain,
% 11.60/1.98      ( r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK3)),u1_struct_0(sK3))
% 11.60/1.98      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1903]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2623,plain,
% 11.60/1.98      ( r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
% 11.60/1.98      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_2621]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2622,plain,
% 11.60/1.98      ( ~ r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK3)),u1_struct_0(sK3))
% 11.60/1.98      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_0]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2625,plain,
% 11.60/1.98      ( r2_hidden(sK0(u1_struct_0(sK3),u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
% 11.60/1.98      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_2622]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1159,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1992,plain,
% 11.60/1.98      ( X0 != X1 | k2_struct_0(sK3) != X1 | k2_struct_0(sK3) = X0 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1159]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2183,plain,
% 11.60/1.98      ( X0 != k2_struct_0(sK3)
% 11.60/1.98      | k2_struct_0(sK3) = X0
% 11.60/1.98      | k2_struct_0(sK3) != k2_struct_0(sK3) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1992]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2904,plain,
% 11.60/1.98      ( u1_struct_0(sK3) != k2_struct_0(sK3)
% 11.60/1.98      | k2_struct_0(sK3) = u1_struct_0(sK3)
% 11.60/1.98      | k2_struct_0(sK3) != k2_struct_0(sK3) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_2183]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1162,plain,
% 11.60/1.98      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 11.60/1.98      theory(equality) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3648,plain,
% 11.60/1.98      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 11.60/1.98      | k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1162]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1851,plain,
% 11.60/1.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_4]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3758,plain,
% 11.60/1.98      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1851]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3759,plain,
% 11.60/1.98      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 11.60/1.98      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_3758]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1163,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.60/1.98      theory(equality) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1846,plain,
% 11.60/1.98      ( m1_subset_1(X0,X1)
% 11.60/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 11.60/1.98      | X0 != X2
% 11.60/1.98      | X1 != k1_zfmisc_1(X3) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1163]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1935,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.60/1.98      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.60/1.98      | X2 != X0
% 11.60/1.98      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1846]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2494,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | k2_struct_0(sK3) != X0
% 11.60/1.98      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1935]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4566,plain,
% 11.60/1.98      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | k2_struct_0(sK3) != u1_struct_0(sK3)
% 11.60/1.98      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_2494]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4567,plain,
% 11.60/1.98      ( k2_struct_0(sK3) != u1_struct_0(sK3)
% 11.60/1.98      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
% 11.60/1.98      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.60/1.98      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_4566]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_5,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.60/1.98      inference(cnf_transformation,[],[f43]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1902,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | r1_tarski(X0,u1_struct_0(sK3)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_5]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_7209,plain,
% 11.60/1.98      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | r1_tarski(k2_struct_0(sK3),u1_struct_0(sK3)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1902]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_7216,plain,
% 11.60/1.98      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.60/1.98      | r1_tarski(k2_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_7209]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4367,plain,
% 11.60/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3)))
% 11.60/1.98      | ~ r1_tarski(X0,k2_struct_0(sK3)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_4]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_7468,plain,
% 11.60/1.98      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3)))
% 11.60/1.98      | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_4367]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_7469,plain,
% 11.60/1.98      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 11.60/1.98      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3)) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_7468]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1160,plain,
% 11.60/1.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,X2) | X2 != X1 ),
% 11.60/1.98      theory(equality) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3392,plain,
% 11.60/1.98      ( ~ r1_tarski(X0,X1)
% 11.60/1.98      | r1_tarski(X0,k2_struct_0(sK3))
% 11.60/1.98      | k2_struct_0(sK3) != X1 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1160]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4445,plain,
% 11.60/1.98      ( ~ r1_tarski(X0,u1_struct_0(sK3))
% 11.60/1.98      | r1_tarski(X0,k2_struct_0(sK3))
% 11.60/1.98      | k2_struct_0(sK3) != u1_struct_0(sK3) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_3392]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_9230,plain,
% 11.60/1.98      ( ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(sK3))
% 11.60/1.98      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3))
% 11.60/1.98      | k2_struct_0(sK3) != u1_struct_0(sK3) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_4445]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_9234,plain,
% 11.60/1.98      ( k2_struct_0(sK3) != u1_struct_0(sK3)
% 11.60/1.98      | r1_tarski(k2_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 11.60/1.98      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3)) = iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_9230]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_10067,plain,
% 11.60/1.98      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 11.60/1.98      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_9250,c_20,c_49,c_67,c_1175,c_1176,c_1183,c_2623,
% 11.60/1.98                 c_2625,c_2904,c_3648,c_3759,c_4567,c_7216,c_7469,c_9234]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_10075,plain,
% 11.60/1.98      ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),X0),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)),X0)
% 11.60/1.98      | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X0) = iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1617,c_10067]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3,plain,
% 11.60/1.98      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 11.60/1.98      inference(cnf_transformation,[],[f42]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1615,plain,
% 11.60/1.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_11288,plain,
% 11.60/1.98      ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0)
% 11.60/1.98      | k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_10075,c_1615]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_19,negated_conjecture,
% 11.60/1.98      ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 11.60/1.98      inference(cnf_transformation,[],[f63]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1922,plain,
% 11.60/1.98      ( ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0)
% 11.60/1.98      | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_3]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1841,plain,
% 11.60/1.98      ( r2_hidden(sK0(X0,k1_xboole_0),X0) | r1_tarski(X0,k1_xboole_0) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1948,plain,
% 11.60/1.98      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k1_orders_2(sK3,k2_struct_0(sK3)))
% 11.60/1.98      | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1841]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2424,plain,
% 11.60/1.98      ( sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1158]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2310,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),a_2_0_orders_2(sK3,X0))
% 11.60/1.98      | sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),sK3,X0) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_634]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_7205,plain,
% 11.60/1.98      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),a_2_0_orders_2(sK3,k2_struct_0(sK3)))
% 11.60/1.98      | sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_2310]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1161,plain,
% 11.60/1.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.60/1.98      theory(equality) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2034,plain,
% 11.60/1.98      ( r2_hidden(X0,X1)
% 11.60/1.98      | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k1_orders_2(sK3,k2_struct_0(sK3)))
% 11.60/1.98      | X1 != k1_orders_2(sK3,k2_struct_0(sK3))
% 11.60/1.98      | X0 != sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1161]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2423,plain,
% 11.60/1.98      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),X0)
% 11.60/1.98      | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k1_orders_2(sK3,k2_struct_0(sK3)))
% 11.60/1.98      | X0 != k1_orders_2(sK3,k2_struct_0(sK3))
% 11.60/1.98      | sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) != sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_2034]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_7246,plain,
% 11.60/1.98      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),a_2_0_orders_2(sK3,k2_struct_0(sK3)))
% 11.60/1.98      | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k1_orders_2(sK3,k2_struct_0(sK3)))
% 11.60/1.98      | a_2_0_orders_2(sK3,k2_struct_0(sK3)) != k1_orders_2(sK3,k2_struct_0(sK3))
% 11.60/1.98      | sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) != sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_2423]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_11356,plain,
% 11.60/1.98      ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0) ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_11288,c_20,c_19,c_49,c_67,c_1175,c_1176,c_1183,c_1922,
% 11.60/1.98                 c_1948,c_2424,c_2621,c_2622,c_2846,c_2904,c_3648,c_3758,
% 11.60/1.98                 c_4566,c_7205,c_7246]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_16,plain,
% 11.60/1.98      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 11.60/1.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.60/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 11.60/1.98      | ~ r2_hidden(X1,X3)
% 11.60/1.98      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 11.60/1.98      | v2_struct_0(X0)
% 11.60/1.98      | ~ v3_orders_2(X0)
% 11.60/1.98      | ~ v4_orders_2(X0)
% 11.60/1.98      | ~ v5_orders_2(X0)
% 11.60/1.98      | ~ l1_orders_2(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f54]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_557,plain,
% 11.60/1.98      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 11.60/1.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.60/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 11.60/1.98      | ~ r2_hidden(X1,X3)
% 11.60/1.98      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 11.60/1.98      | v2_struct_0(X0)
% 11.60/1.98      | ~ v3_orders_2(X0)
% 11.60/1.98      | ~ v4_orders_2(X0)
% 11.60/1.98      | ~ l1_orders_2(X0)
% 11.60/1.98      | sK3 != X0 ),
% 11.60/1.98      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_558,plain,
% 11.60/1.98      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 11.60/1.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.60/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | ~ r2_hidden(X0,X2)
% 11.60/1.98      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
% 11.60/1.98      | v2_struct_0(sK3)
% 11.60/1.98      | ~ v3_orders_2(sK3)
% 11.60/1.98      | ~ v4_orders_2(sK3)
% 11.60/1.98      | ~ l1_orders_2(sK3) ),
% 11.60/1.98      inference(unflattening,[status(thm)],[c_557]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_562,plain,
% 11.60/1.98      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 11.60/1.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 11.60/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | ~ r2_hidden(X0,X2)
% 11.60/1.98      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2)) ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_558,c_24,c_23,c_22,c_20]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1612,plain,
% 11.60/1.98      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
% 11.60/1.98      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 11.60/1.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.60/1.98      | r2_hidden(X0,X2) != iProver_top
% 11.60/1.98      | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_562]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1705,plain,
% 11.60/1.98      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
% 11.60/1.98      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 11.60/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.60/1.98      | r2_hidden(X0,X2) != iProver_top
% 11.60/1.98      | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_1612,c_770]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_8,plain,
% 11.60/1.98      ( ~ r2_orders_2(X0,X1,X1)
% 11.60/1.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.60/1.98      | ~ l1_orders_2(X0) ),
% 11.60/1.98      inference(cnf_transformation,[],[f64]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_774,plain,
% 11.60/1.98      ( ~ r2_orders_2(X0,X1,X1)
% 11.60/1.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.60/1.98      | sK3 != X0 ),
% 11.60/1.98      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_775,plain,
% 11.60/1.98      ( ~ r2_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 11.60/1.98      inference(unflattening,[status(thm)],[c_774]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1604,plain,
% 11.60/1.98      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 11.60/1.98      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_775]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1643,plain,
% 11.60/1.98      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 11.60/1.98      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_1604,c_770]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2225,plain,
% 11.60/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.60/1.98      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) != iProver_top
% 11.60/1.98      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 11.60/1.98      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_1705,c_1643]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_18,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 11.60/1.98      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 11.60/1.98      | v2_struct_0(X1)
% 11.60/1.98      | ~ v3_orders_2(X1)
% 11.60/1.98      | ~ v4_orders_2(X1)
% 11.60/1.98      | ~ v5_orders_2(X1)
% 11.60/1.98      | ~ l1_orders_2(X1) ),
% 11.60/1.98      inference(cnf_transformation,[],[f52]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_608,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | m1_subset_1(sK2(X2,X1,X0),u1_struct_0(X1))
% 11.60/1.98      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 11.60/1.98      | v2_struct_0(X1)
% 11.60/1.98      | ~ v3_orders_2(X1)
% 11.60/1.98      | ~ v4_orders_2(X1)
% 11.60/1.98      | ~ l1_orders_2(X1)
% 11.60/1.98      | sK3 != X1 ),
% 11.60/1.98      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_609,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 11.60/1.98      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0))
% 11.60/1.98      | v2_struct_0(sK3)
% 11.60/1.98      | ~ v3_orders_2(sK3)
% 11.60/1.98      | ~ v4_orders_2(sK3)
% 11.60/1.98      | ~ l1_orders_2(sK3) ),
% 11.60/1.98      inference(unflattening,[status(thm)],[c_608]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_613,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3))
% 11.60/1.98      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X0)) ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_609,c_24,c_23,c_22,c_20]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1610,plain,
% 11.60/1.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 11.60/1.98      | m1_subset_1(sK2(X1,sK3,X0),u1_struct_0(sK3)) = iProver_top
% 11.60/1.98      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top ),
% 11.60/1.98      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_1671,plain,
% 11.60/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.60/1.98      | m1_subset_1(sK2(X1,sK3,X0),k2_struct_0(sK3)) = iProver_top
% 11.60/1.98      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_1610,c_770]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_3277,plain,
% 11.60/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.60/1.98      | r2_hidden(X1,a_2_0_orders_2(sK3,X0)) != iProver_top
% 11.60/1.98      | r2_hidden(sK2(X1,sK3,X0),X0) != iProver_top ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_2225,c_1671]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_11363,plain,
% 11.60/1.98      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.60/1.98      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 11.60/1.98      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k2_struct_0(sK3)) != iProver_top ),
% 11.60/1.98      inference(superposition,[status(thm)],[c_11356,c_3277]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_11389,plain,
% 11.60/1.98      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 11.60/1.98      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 11.60/1.98      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k2_struct_0(sK3)) != iProver_top ),
% 11.60/1.98      inference(light_normalisation,[status(thm)],[c_11363,c_2846]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_11421,plain,
% 11.60/1.98      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3)))
% 11.60/1.98      | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k1_orders_2(sK3,k2_struct_0(sK3)))
% 11.60/1.98      | ~ r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3)),k1_xboole_0),k2_struct_0(sK3)) ),
% 11.60/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_11389]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2063,plain,
% 11.60/1.98      ( ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X0)
% 11.60/1.98      | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X1)
% 11.60/1.98      | X1 != X0 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1160]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_4065,plain,
% 11.60/1.98      ( ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),X0)
% 11.60/1.98      | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k2_struct_0(sK3))
% 11.60/1.98      | k2_struct_0(sK3) != X0 ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_2063]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_7422,plain,
% 11.60/1.98      ( ~ r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),u1_struct_0(sK3))
% 11.60/1.98      | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),k2_struct_0(sK3))
% 11.60/1.98      | k2_struct_0(sK3) != u1_struct_0(sK3) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_4065]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_11,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | v2_struct_0(X1)
% 11.60/1.98      | ~ v3_orders_2(X1)
% 11.60/1.98      | ~ v4_orders_2(X1)
% 11.60/1.98      | ~ v5_orders_2(X1)
% 11.60/1.98      | ~ l1_orders_2(X1) ),
% 11.60/1.98      inference(cnf_transformation,[],[f50]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_698,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.98      | v2_struct_0(X1)
% 11.60/1.98      | ~ v3_orders_2(X1)
% 11.60/1.98      | ~ v4_orders_2(X1)
% 11.60/1.98      | ~ l1_orders_2(X1)
% 11.60/1.98      | sK3 != X1 ),
% 11.60/1.98      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_699,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | v2_struct_0(sK3)
% 11.60/1.98      | ~ v3_orders_2(sK3)
% 11.60/1.98      | ~ v4_orders_2(sK3)
% 11.60/1.98      | ~ l1_orders_2(sK3) ),
% 11.60/1.98      inference(unflattening,[status(thm)],[c_698]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_703,plain,
% 11.60/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 11.60/1.98      inference(global_propositional_subsumption,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_699,c_24,c_23,c_22,c_20]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_7204,plain,
% 11.60/1.98      ( m1_subset_1(k1_orders_2(sK3,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_703]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(c_2069,plain,
% 11.60/1.98      ( ~ m1_subset_1(k1_orders_2(sK3,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.60/1.98      | r1_tarski(k1_orders_2(sK3,k2_struct_0(sK3)),u1_struct_0(sK3)) ),
% 11.60/1.98      inference(instantiation,[status(thm)],[c_1902]) ).
% 11.60/1.98  
% 11.60/1.98  cnf(contradiction,plain,
% 11.60/1.98      ( $false ),
% 11.60/1.98      inference(minisat,
% 11.60/1.98                [status(thm)],
% 11.60/1.98                [c_26673,c_11421,c_9230,c_7468,c_7422,c_7204,c_7209,
% 11.60/1.98                 c_4566,c_3758,c_3648,c_2904,c_2622,c_2621,c_2069,c_1948,
% 11.60/1.98                 c_1922,c_1183,c_1176,c_1175,c_67,c_49,c_19,c_20]) ).
% 11.60/1.98  
% 11.60/1.98  
% 11.60/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.60/1.98  
% 11.60/1.98  ------                               Statistics
% 11.60/1.98  
% 11.60/1.98  ------ Selected
% 11.60/1.98  
% 11.60/1.98  total_time:                             1.084
% 11.60/1.98  
%------------------------------------------------------------------------------
