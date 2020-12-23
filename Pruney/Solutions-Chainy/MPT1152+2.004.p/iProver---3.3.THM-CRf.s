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
% DateTime   : Thu Dec  3 12:12:10 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 770 expanded)
%              Number of clauses        :   75 ( 266 expanded)
%              Number of leaves         :   17 ( 152 expanded)
%              Depth                    :   24
%              Number of atoms          :  583 (3417 expanded)
%              Number of equality atoms :  223 ( 832 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f43,plain,
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

fof(f44,plain,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f43])).

fof(f71,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

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

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f34])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f41,plain,(
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

fof(f40,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f41,f40])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(nnf_transformation,[],[f23])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

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

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_746,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_15,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_753,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1157,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_746,c_753])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_762,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1264,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_1157,c_762])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_754,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3442,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_754])).

cnf(c_3499,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3442,c_1264])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_29,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_30,plain,
    ( v4_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_31,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_32,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3811,plain,
    ( m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3499,c_28,c_29,c_30,c_31,c_32])).

cnf(c_3812,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3811])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_764,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_747,plain,
    ( r2_hidden(X0,a_2_1_orders_2(X1,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1481,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_747])).

cnf(c_1503,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1481,c_1264])).

cnf(c_1804,plain,
    ( m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1503,c_28,c_29,c_30,c_31,c_32])).

cnf(c_1805,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1804])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_765,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2058,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_765])).

cnf(c_51,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_53,plain,
    ( l1_orders_2(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_9,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_759,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1483,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_759])).

cnf(c_2490,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2058,c_28,c_32,c_53,c_1483])).

cnf(c_2491,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2490])).

cnf(c_19,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_749,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_757,plain,
    ( r2_orders_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2601,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_757])).

cnf(c_2653,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | r2_orders_2(sK3,X0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2601,c_32])).

cnf(c_2654,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2653])).

cnf(c_2663,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),sK2(X0,sK3,X1)) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_2654])).

cnf(c_2919,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_749,c_2663])).

cnf(c_2920,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2919,c_1264])).

cnf(c_3671,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2920,c_28,c_29,c_30,c_31,c_32,c_1503])).

cnf(c_3680,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2491,c_3671])).

cnf(c_7,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_761,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1484,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_761])).

cnf(c_4024,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3680,c_32,c_53,c_1484])).

cnf(c_1676,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1484,c_32,c_53])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_755,plain,
    ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3175,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_755])).

cnf(c_3685,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3175,c_28,c_29,c_30,c_31,c_32])).

cnf(c_3686,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3685])).

cnf(c_3695,plain,
    ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1676,c_3686])).

cnf(c_4030,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4024,c_3695])).

cnf(c_4035,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | m1_subset_1(k2_orders_2(sK3,k2_struct_0(sK3)),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_764,c_4030])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_250,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_1117,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_1191,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
    | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_249,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1192,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_4647,plain,
    ( m1_subset_1(k2_orders_2(sK3,k2_struct_0(sK3)),k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4035,c_22,c_1191,c_1192])).

cnf(c_4656,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3812,c_4647])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4656,c_1484,c_53,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:36:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.56/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.02  
% 3.56/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.56/1.02  
% 3.56/1.02  ------  iProver source info
% 3.56/1.02  
% 3.56/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.56/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.56/1.02  git: non_committed_changes: false
% 3.56/1.02  git: last_make_outside_of_git: false
% 3.56/1.02  
% 3.56/1.02  ------ 
% 3.56/1.02  ------ Parsing...
% 3.56/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.56/1.02  
% 3.56/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.56/1.02  
% 3.56/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.56/1.02  
% 3.56/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/1.02  ------ Proving...
% 3.56/1.02  ------ Problem Properties 
% 3.56/1.02  
% 3.56/1.02  
% 3.56/1.02  clauses                                 28
% 3.56/1.02  conjectures                             6
% 3.56/1.02  EPR                                     10
% 3.56/1.02  Horn                                    15
% 3.56/1.02  unary                                   6
% 3.56/1.02  binary                                  3
% 3.56/1.02  lits                                    117
% 3.56/1.02  lits eq                                 7
% 3.56/1.02  fd_pure                                 0
% 3.56/1.02  fd_pseudo                               0
% 3.56/1.02  fd_cond                                 2
% 3.56/1.02  fd_pseudo_cond                          1
% 3.56/1.02  AC symbols                              0
% 3.56/1.02  
% 3.56/1.02  ------ Input Options Time Limit: Unbounded
% 3.56/1.02  
% 3.56/1.02  
% 3.56/1.02  ------ 
% 3.56/1.02  Current options:
% 3.56/1.02  ------ 
% 3.56/1.02  
% 3.56/1.02  
% 3.56/1.02  
% 3.56/1.02  
% 3.56/1.02  ------ Proving...
% 3.56/1.02  
% 3.56/1.02  
% 3.56/1.02  % SZS status Theorem for theBenchmark.p
% 3.56/1.02  
% 3.56/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.56/1.02  
% 3.56/1.02  fof(f12,conjecture,(
% 3.56/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f13,negated_conjecture,(
% 3.56/1.02    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 3.56/1.02    inference(negated_conjecture,[],[f12])).
% 3.56/1.02  
% 3.56/1.02  fof(f31,plain,(
% 3.56/1.02    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.56/1.02    inference(ennf_transformation,[],[f13])).
% 3.56/1.02  
% 3.56/1.02  fof(f32,plain,(
% 3.56/1.02    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.56/1.02    inference(flattening,[],[f31])).
% 3.56/1.02  
% 3.56/1.02  fof(f43,plain,(
% 3.56/1.02    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 3.56/1.02    introduced(choice_axiom,[])).
% 3.56/1.02  
% 3.56/1.02  fof(f44,plain,(
% 3.56/1.02    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 3.56/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f43])).
% 3.56/1.02  
% 3.56/1.02  fof(f71,plain,(
% 3.56/1.02    l1_orders_2(sK3)),
% 3.56/1.02    inference(cnf_transformation,[],[f44])).
% 3.56/1.02  
% 3.56/1.02  fof(f10,axiom,(
% 3.56/1.02    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f28,plain,(
% 3.56/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.56/1.02    inference(ennf_transformation,[],[f10])).
% 3.56/1.02  
% 3.56/1.02  fof(f60,plain,(
% 3.56/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f28])).
% 3.56/1.02  
% 3.56/1.02  fof(f3,axiom,(
% 3.56/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f17,plain,(
% 3.56/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.56/1.02    inference(ennf_transformation,[],[f3])).
% 3.56/1.02  
% 3.56/1.02  fof(f51,plain,(
% 3.56/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f17])).
% 3.56/1.02  
% 3.56/1.02  fof(f9,axiom,(
% 3.56/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f26,plain,(
% 3.56/1.02    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.56/1.02    inference(ennf_transformation,[],[f9])).
% 3.56/1.02  
% 3.56/1.02  fof(f27,plain,(
% 3.56/1.02    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.56/1.02    inference(flattening,[],[f26])).
% 3.56/1.02  
% 3.56/1.02  fof(f59,plain,(
% 3.56/1.02    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f27])).
% 3.56/1.02  
% 3.56/1.02  fof(f67,plain,(
% 3.56/1.02    ~v2_struct_0(sK3)),
% 3.56/1.02    inference(cnf_transformation,[],[f44])).
% 3.56/1.02  
% 3.56/1.02  fof(f68,plain,(
% 3.56/1.02    v3_orders_2(sK3)),
% 3.56/1.02    inference(cnf_transformation,[],[f44])).
% 3.56/1.02  
% 3.56/1.02  fof(f69,plain,(
% 3.56/1.02    v4_orders_2(sK3)),
% 3.56/1.02    inference(cnf_transformation,[],[f44])).
% 3.56/1.02  
% 3.56/1.02  fof(f70,plain,(
% 3.56/1.02    v5_orders_2(sK3)),
% 3.56/1.02    inference(cnf_transformation,[],[f44])).
% 3.56/1.02  
% 3.56/1.02  fof(f2,axiom,(
% 3.56/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f15,plain,(
% 3.56/1.02    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.56/1.02    inference(ennf_transformation,[],[f2])).
% 3.56/1.02  
% 3.56/1.02  fof(f16,plain,(
% 3.56/1.02    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.56/1.02    inference(flattening,[],[f15])).
% 3.56/1.02  
% 3.56/1.02  fof(f34,plain,(
% 3.56/1.02    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)))),
% 3.56/1.02    introduced(choice_axiom,[])).
% 3.56/1.02  
% 3.56/1.02  fof(f35,plain,(
% 3.56/1.02    ! [X0,X1] : ((r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.56/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f34])).
% 3.56/1.02  
% 3.56/1.02  fof(f50,plain,(
% 3.56/1.02    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.56/1.02    inference(cnf_transformation,[],[f35])).
% 3.56/1.02  
% 3.56/1.02  fof(f11,axiom,(
% 3.56/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f29,plain,(
% 3.56/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 3.56/1.02    inference(ennf_transformation,[],[f11])).
% 3.56/1.02  
% 3.56/1.02  fof(f30,plain,(
% 3.56/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.56/1.02    inference(flattening,[],[f29])).
% 3.56/1.02  
% 3.56/1.02  fof(f38,plain,(
% 3.56/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.56/1.02    inference(nnf_transformation,[],[f30])).
% 3.56/1.02  
% 3.56/1.02  fof(f39,plain,(
% 3.56/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.56/1.02    inference(rectify,[],[f38])).
% 3.56/1.02  
% 3.56/1.02  fof(f41,plain,(
% 3.56/1.02    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.56/1.02    introduced(choice_axiom,[])).
% 3.56/1.02  
% 3.56/1.02  fof(f40,plain,(
% 3.56/1.02    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 3.56/1.02    introduced(choice_axiom,[])).
% 3.56/1.02  
% 3.56/1.02  fof(f42,plain,(
% 3.56/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.56/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f41,f40])).
% 3.56/1.02  
% 3.56/1.02  fof(f61,plain,(
% 3.56/1.02    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f42])).
% 3.56/1.02  
% 3.56/1.02  fof(f1,axiom,(
% 3.56/1.02    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f14,plain,(
% 3.56/1.02    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.56/1.02    inference(ennf_transformation,[],[f1])).
% 3.56/1.02  
% 3.56/1.02  fof(f33,plain,(
% 3.56/1.02    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.56/1.02    inference(nnf_transformation,[],[f14])).
% 3.56/1.02  
% 3.56/1.02  fof(f45,plain,(
% 3.56/1.02    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f33])).
% 3.56/1.02  
% 3.56/1.02  fof(f6,axiom,(
% 3.56/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f21,plain,(
% 3.56/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.56/1.02    inference(ennf_transformation,[],[f6])).
% 3.56/1.02  
% 3.56/1.02  fof(f22,plain,(
% 3.56/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.56/1.02    inference(flattening,[],[f21])).
% 3.56/1.02  
% 3.56/1.02  fof(f54,plain,(
% 3.56/1.02    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f22])).
% 3.56/1.02  
% 3.56/1.02  fof(f63,plain,(
% 3.56/1.02    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f42])).
% 3.56/1.02  
% 3.56/1.02  fof(f7,axiom,(
% 3.56/1.02    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f23,plain,(
% 3.56/1.02    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.56/1.02    inference(ennf_transformation,[],[f7])).
% 3.56/1.02  
% 3.56/1.02  fof(f36,plain,(
% 3.56/1.02    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.56/1.02    inference(nnf_transformation,[],[f23])).
% 3.56/1.02  
% 3.56/1.02  fof(f37,plain,(
% 3.56/1.02    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.56/1.02    inference(flattening,[],[f36])).
% 3.56/1.02  
% 3.56/1.02  fof(f56,plain,(
% 3.56/1.02    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f37])).
% 3.56/1.02  
% 3.56/1.02  fof(f73,plain,(
% 3.56/1.02    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.56/1.02    inference(equality_resolution,[],[f56])).
% 3.56/1.02  
% 3.56/1.02  fof(f4,axiom,(
% 3.56/1.02    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f18,plain,(
% 3.56/1.02    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 3.56/1.02    inference(ennf_transformation,[],[f4])).
% 3.56/1.02  
% 3.56/1.02  fof(f52,plain,(
% 3.56/1.02    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f18])).
% 3.56/1.02  
% 3.56/1.02  fof(f8,axiom,(
% 3.56/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f24,plain,(
% 3.56/1.02    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.56/1.02    inference(ennf_transformation,[],[f8])).
% 3.56/1.02  
% 3.56/1.02  fof(f25,plain,(
% 3.56/1.02    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.56/1.02    inference(flattening,[],[f24])).
% 3.56/1.02  
% 3.56/1.02  fof(f58,plain,(
% 3.56/1.02    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f25])).
% 3.56/1.02  
% 3.56/1.02  fof(f72,plain,(
% 3.56/1.02    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))),
% 3.56/1.02    inference(cnf_transformation,[],[f44])).
% 3.56/1.02  
% 3.56/1.02  cnf(c_23,negated_conjecture,
% 3.56/1.02      ( l1_orders_2(sK3) ),
% 3.56/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_746,plain,
% 3.56/1.02      ( l1_orders_2(sK3) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_15,plain,
% 3.56/1.02      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.56/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_753,plain,
% 3.56/1.02      ( l1_orders_2(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1157,plain,
% 3.56/1.02      ( l1_struct_0(sK3) = iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_746,c_753]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_6,plain,
% 3.56/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.56/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_762,plain,
% 3.56/1.02      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.56/1.02      | l1_struct_0(X0) != iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1264,plain,
% 3.56/1.02      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_1157,c_762]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_14,plain,
% 3.56/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.56/1.02      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.56/1.02      | ~ v3_orders_2(X1)
% 3.56/1.02      | ~ v4_orders_2(X1)
% 3.56/1.02      | ~ v5_orders_2(X1)
% 3.56/1.02      | ~ l1_orders_2(X1)
% 3.56/1.02      | v2_struct_0(X1) ),
% 3.56/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_754,plain,
% 3.56/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.56/1.02      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.56/1.02      | v3_orders_2(X1) != iProver_top
% 3.56/1.02      | v4_orders_2(X1) != iProver_top
% 3.56/1.02      | v5_orders_2(X1) != iProver_top
% 3.56/1.02      | l1_orders_2(X1) != iProver_top
% 3.56/1.02      | v2_struct_0(X1) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_3442,plain,
% 3.56/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.56/1.02      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.56/1.02      | v3_orders_2(sK3) != iProver_top
% 3.56/1.02      | v4_orders_2(sK3) != iProver_top
% 3.56/1.02      | v5_orders_2(sK3) != iProver_top
% 3.56/1.02      | l1_orders_2(sK3) != iProver_top
% 3.56/1.02      | v2_struct_0(sK3) = iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_1264,c_754]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_3499,plain,
% 3.56/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.56/1.02      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.56/1.02      | v3_orders_2(sK3) != iProver_top
% 3.56/1.02      | v4_orders_2(sK3) != iProver_top
% 3.56/1.02      | v5_orders_2(sK3) != iProver_top
% 3.56/1.02      | l1_orders_2(sK3) != iProver_top
% 3.56/1.02      | v2_struct_0(sK3) = iProver_top ),
% 3.56/1.02      inference(light_normalisation,[status(thm)],[c_3442,c_1264]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_27,negated_conjecture,
% 3.56/1.02      ( ~ v2_struct_0(sK3) ),
% 3.56/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_28,plain,
% 3.56/1.02      ( v2_struct_0(sK3) != iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_26,negated_conjecture,
% 3.56/1.02      ( v3_orders_2(sK3) ),
% 3.56/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_29,plain,
% 3.56/1.02      ( v3_orders_2(sK3) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_25,negated_conjecture,
% 3.56/1.02      ( v4_orders_2(sK3) ),
% 3.56/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_30,plain,
% 3.56/1.02      ( v4_orders_2(sK3) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_24,negated_conjecture,
% 3.56/1.02      ( v5_orders_2(sK3) ),
% 3.56/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_31,plain,
% 3.56/1.02      ( v5_orders_2(sK3) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_32,plain,
% 3.56/1.02      ( l1_orders_2(sK3) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_3811,plain,
% 3.56/1.02      ( m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.56/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.56/1.02      inference(global_propositional_subsumption,
% 3.56/1.02                [status(thm)],
% 3.56/1.02                [c_3499,c_28,c_29,c_30,c_31,c_32]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_3812,plain,
% 3.56/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.56/1.02      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 3.56/1.02      inference(renaming,[status(thm)],[c_3811]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_4,plain,
% 3.56/1.02      ( r2_hidden(sK0(X0,X1),X1)
% 3.56/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 3.56/1.02      | k1_xboole_0 = X1 ),
% 3.56/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_764,plain,
% 3.56/1.02      ( k1_xboole_0 = X0
% 3.56/1.02      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 3.56/1.02      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_21,plain,
% 3.56/1.02      ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 3.56/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.56/1.02      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 3.56/1.02      | ~ v3_orders_2(X1)
% 3.56/1.02      | ~ v4_orders_2(X1)
% 3.56/1.02      | ~ v5_orders_2(X1)
% 3.56/1.02      | ~ l1_orders_2(X1)
% 3.56/1.02      | v2_struct_0(X1) ),
% 3.56/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_747,plain,
% 3.56/1.02      ( r2_hidden(X0,a_2_1_orders_2(X1,X2)) != iProver_top
% 3.56/1.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.56/1.02      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top
% 3.56/1.02      | v3_orders_2(X1) != iProver_top
% 3.56/1.02      | v4_orders_2(X1) != iProver_top
% 3.56/1.02      | v5_orders_2(X1) != iProver_top
% 3.56/1.02      | l1_orders_2(X1) != iProver_top
% 3.56/1.02      | v2_struct_0(X1) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1481,plain,
% 3.56/1.02      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.56/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.56/1.02      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
% 3.56/1.02      | v3_orders_2(sK3) != iProver_top
% 3.56/1.02      | v4_orders_2(sK3) != iProver_top
% 3.56/1.02      | v5_orders_2(sK3) != iProver_top
% 3.56/1.02      | l1_orders_2(sK3) != iProver_top
% 3.56/1.02      | v2_struct_0(sK3) = iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_1264,c_747]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1503,plain,
% 3.56/1.02      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.56/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.56/1.02      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
% 3.56/1.02      | v3_orders_2(sK3) != iProver_top
% 3.56/1.02      | v4_orders_2(sK3) != iProver_top
% 3.56/1.02      | v5_orders_2(sK3) != iProver_top
% 3.56/1.02      | l1_orders_2(sK3) != iProver_top
% 3.56/1.02      | v2_struct_0(sK3) = iProver_top ),
% 3.56/1.02      inference(light_normalisation,[status(thm)],[c_1481,c_1264]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1804,plain,
% 3.56/1.02      ( m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
% 3.56/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.56/1.02      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 3.56/1.02      inference(global_propositional_subsumption,
% 3.56/1.02                [status(thm)],
% 3.56/1.02                [c_1503,c_28,c_29,c_30,c_31,c_32]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1805,plain,
% 3.56/1.02      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.56/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.56/1.02      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top ),
% 3.56/1.02      inference(renaming,[status(thm)],[c_1804]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_3,plain,
% 3.56/1.02      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 3.56/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_765,plain,
% 3.56/1.02      ( r2_hidden(X0,X1) = iProver_top
% 3.56/1.02      | m1_subset_1(X0,X1) != iProver_top
% 3.56/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_2058,plain,
% 3.56/1.02      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.56/1.02      | r2_hidden(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
% 3.56/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.56/1.02      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_1805,c_765]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_51,plain,
% 3.56/1.02      ( l1_orders_2(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_53,plain,
% 3.56/1.02      ( l1_orders_2(sK3) != iProver_top
% 3.56/1.02      | l1_struct_0(sK3) = iProver_top ),
% 3.56/1.02      inference(instantiation,[status(thm)],[c_51]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_9,plain,
% 3.56/1.02      ( v2_struct_0(X0)
% 3.56/1.02      | ~ l1_struct_0(X0)
% 3.56/1.02      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.56/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_759,plain,
% 3.56/1.02      ( v2_struct_0(X0) = iProver_top
% 3.56/1.02      | l1_struct_0(X0) != iProver_top
% 3.56/1.02      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1483,plain,
% 3.56/1.02      ( v2_struct_0(sK3) = iProver_top
% 3.56/1.02      | l1_struct_0(sK3) != iProver_top
% 3.56/1.02      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_1264,c_759]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_2490,plain,
% 3.56/1.02      ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.56/1.02      | r2_hidden(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
% 3.56/1.02      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 3.56/1.02      inference(global_propositional_subsumption,
% 3.56/1.02                [status(thm)],
% 3.56/1.02                [c_2058,c_28,c_32,c_53,c_1483]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_2491,plain,
% 3.56/1.02      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.56/1.02      | r2_hidden(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
% 3.56/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.56/1.02      inference(renaming,[status(thm)],[c_2490]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_19,plain,
% 3.56/1.02      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 3.56/1.02      | ~ r2_hidden(X3,X2)
% 3.56/1.02      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 3.56/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.56/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.56/1.02      | ~ v3_orders_2(X0)
% 3.56/1.02      | ~ v4_orders_2(X0)
% 3.56/1.02      | ~ v5_orders_2(X0)
% 3.56/1.02      | ~ l1_orders_2(X0)
% 3.56/1.02      | v2_struct_0(X0) ),
% 3.56/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_749,plain,
% 3.56/1.02      ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
% 3.56/1.02      | r2_hidden(X3,X2) != iProver_top
% 3.56/1.02      | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
% 3.56/1.02      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.56/1.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.56/1.02      | v3_orders_2(X0) != iProver_top
% 3.56/1.02      | v4_orders_2(X0) != iProver_top
% 3.56/1.02      | v5_orders_2(X0) != iProver_top
% 3.56/1.02      | l1_orders_2(X0) != iProver_top
% 3.56/1.02      | v2_struct_0(X0) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_11,plain,
% 3.56/1.02      ( ~ r2_orders_2(X0,X1,X1)
% 3.56/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.56/1.02      | ~ l1_orders_2(X0) ),
% 3.56/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_757,plain,
% 3.56/1.02      ( r2_orders_2(X0,X1,X1) != iProver_top
% 3.56/1.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.56/1.02      | l1_orders_2(X0) != iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_2601,plain,
% 3.56/1.02      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 3.56/1.02      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.56/1.02      | l1_orders_2(sK3) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_1264,c_757]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_2653,plain,
% 3.56/1.02      ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.56/1.02      | r2_orders_2(sK3,X0,X0) != iProver_top ),
% 3.56/1.02      inference(global_propositional_subsumption,
% 3.56/1.02                [status(thm)],
% 3.56/1.02                [c_2601,c_32]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_2654,plain,
% 3.56/1.02      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 3.56/1.02      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 3.56/1.02      inference(renaming,[status(thm)],[c_2653]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_2663,plain,
% 3.56/1.02      ( r2_orders_2(sK3,sK2(X0,sK3,X1),sK2(X0,sK3,X1)) != iProver_top
% 3.56/1.02      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.56/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_1805,c_2654]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_2919,plain,
% 3.56/1.02      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.56/1.02      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 3.56/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.56/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.56/1.02      | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) != iProver_top
% 3.56/1.02      | v3_orders_2(sK3) != iProver_top
% 3.56/1.02      | v4_orders_2(sK3) != iProver_top
% 3.56/1.02      | v5_orders_2(sK3) != iProver_top
% 3.56/1.02      | l1_orders_2(sK3) != iProver_top
% 3.56/1.02      | v2_struct_0(sK3) = iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_749,c_2663]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_2920,plain,
% 3.56/1.02      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.56/1.02      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 3.56/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.56/1.02      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) != iProver_top
% 3.56/1.02      | v3_orders_2(sK3) != iProver_top
% 3.56/1.02      | v4_orders_2(sK3) != iProver_top
% 3.56/1.02      | v5_orders_2(sK3) != iProver_top
% 3.56/1.02      | l1_orders_2(sK3) != iProver_top
% 3.56/1.02      | v2_struct_0(sK3) = iProver_top ),
% 3.56/1.02      inference(light_normalisation,[status(thm)],[c_2919,c_1264]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_3671,plain,
% 3.56/1.02      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 3.56/1.02      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 3.56/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.56/1.02      inference(global_propositional_subsumption,
% 3.56/1.02                [status(thm)],
% 3.56/1.02                [c_2920,c_28,c_29,c_30,c_31,c_32,c_1503]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_3680,plain,
% 3.56/1.02      ( r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.56/1.02      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_2491,c_3671]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_7,plain,
% 3.56/1.02      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.56/1.02      | ~ l1_struct_0(X0) ),
% 3.56/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_761,plain,
% 3.56/1.02      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.56/1.02      | l1_struct_0(X0) != iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1484,plain,
% 3.56/1.02      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.56/1.02      | l1_struct_0(sK3) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_1264,c_761]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_4024,plain,
% 3.56/1.02      ( r2_hidden(X0,a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 3.56/1.02      inference(global_propositional_subsumption,
% 3.56/1.02                [status(thm)],
% 3.56/1.02                [c_3680,c_32,c_53,c_1484]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1676,plain,
% 3.56/1.02      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 3.56/1.02      inference(global_propositional_subsumption,
% 3.56/1.02                [status(thm)],
% 3.56/1.02                [c_1484,c_32,c_53]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_13,plain,
% 3.56/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.56/1.02      | ~ v3_orders_2(X1)
% 3.56/1.02      | ~ v4_orders_2(X1)
% 3.56/1.02      | ~ v5_orders_2(X1)
% 3.56/1.02      | ~ l1_orders_2(X1)
% 3.56/1.02      | v2_struct_0(X1)
% 3.56/1.02      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 3.56/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_755,plain,
% 3.56/1.02      ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
% 3.56/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.56/1.02      | v3_orders_2(X0) != iProver_top
% 3.56/1.02      | v4_orders_2(X0) != iProver_top
% 3.56/1.02      | v5_orders_2(X0) != iProver_top
% 3.56/1.02      | l1_orders_2(X0) != iProver_top
% 3.56/1.02      | v2_struct_0(X0) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_3175,plain,
% 3.56/1.02      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 3.56/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.56/1.02      | v3_orders_2(sK3) != iProver_top
% 3.56/1.02      | v4_orders_2(sK3) != iProver_top
% 3.56/1.02      | v5_orders_2(sK3) != iProver_top
% 3.56/1.02      | l1_orders_2(sK3) != iProver_top
% 3.56/1.02      | v2_struct_0(sK3) = iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_1264,c_755]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_3685,plain,
% 3.56/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.56/1.02      | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
% 3.56/1.02      inference(global_propositional_subsumption,
% 3.56/1.02                [status(thm)],
% 3.56/1.02                [c_3175,c_28,c_29,c_30,c_31,c_32]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_3686,plain,
% 3.56/1.02      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 3.56/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.56/1.02      inference(renaming,[status(thm)],[c_3685]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_3695,plain,
% 3.56/1.02      ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_1676,c_3686]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_4030,plain,
% 3.56/1.02      ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 3.56/1.02      inference(light_normalisation,[status(thm)],[c_4024,c_3695]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_4035,plain,
% 3.56/1.02      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 3.56/1.02      | m1_subset_1(k2_orders_2(sK3,k2_struct_0(sK3)),k1_zfmisc_1(X0)) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_764,c_4030]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_22,negated_conjecture,
% 3.56/1.02      ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.56/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_250,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1117,plain,
% 3.56/1.02      ( k2_orders_2(sK3,k2_struct_0(sK3)) != X0
% 3.56/1.02      | k1_xboole_0 != X0
% 3.56/1.02      | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.56/1.02      inference(instantiation,[status(thm)],[c_250]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1191,plain,
% 3.56/1.02      ( k2_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
% 3.56/1.02      | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3))
% 3.56/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.56/1.02      inference(instantiation,[status(thm)],[c_1117]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_249,plain,( X0 = X0 ),theory(equality) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1192,plain,
% 3.56/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 3.56/1.02      inference(instantiation,[status(thm)],[c_249]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_4647,plain,
% 3.56/1.02      ( m1_subset_1(k2_orders_2(sK3,k2_struct_0(sK3)),k1_zfmisc_1(X0)) != iProver_top ),
% 3.56/1.02      inference(global_propositional_subsumption,
% 3.56/1.02                [status(thm)],
% 3.56/1.02                [c_4035,c_22,c_1191,c_1192]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_4656,plain,
% 3.56/1.02      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_3812,c_4647]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(contradiction,plain,
% 3.56/1.02      ( $false ),
% 3.56/1.02      inference(minisat,[status(thm)],[c_4656,c_1484,c_53,c_32]) ).
% 3.56/1.02  
% 3.56/1.02  
% 3.56/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.56/1.02  
% 3.56/1.02  ------                               Statistics
% 3.56/1.02  
% 3.56/1.02  ------ Selected
% 3.56/1.02  
% 3.56/1.02  total_time:                             0.222
% 3.56/1.02  
%------------------------------------------------------------------------------
