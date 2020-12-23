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
% DateTime   : Thu Dec  3 12:12:07 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 964 expanded)
%              Number of clauses        :   81 ( 325 expanded)
%              Number of leaves         :   16 ( 196 expanded)
%              Depth                    :   26
%              Number of atoms          :  631 (4412 expanded)
%              Number of equality atoms :  280 (1118 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
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

fof(f30,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f29])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,
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

fof(f39,plain,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f38])).

fof(f64,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
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
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

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
    inference(rectify,[],[f33])).

fof(f36,plain,(
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

fof(f35,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f49])).

cnf(c_6,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_681,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_686,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_701,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_686,c_0])).

cnf(c_21,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_667,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_674,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1172,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_667,c_674])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_680,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1411,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_1172,c_680])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_676,plain,
    ( a_2_0_orders_2(X0,X1) = k1_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2202,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_676])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,plain,
    ( v4_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_30,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2410,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2202,c_26,c_27,c_28,c_29,c_30])).

cnf(c_2411,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2410])).

cnf(c_2418,plain,
    ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_701,c_2411])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_669,plain,
    ( sK2(X0,X1,X2) = X0
    | r2_hidden(X0,a_2_0_orders_2(X1,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2539,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2418,c_669])).

cnf(c_2540,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2539,c_1411])).

cnf(c_2545,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | sK2(X0,sK3,k2_struct_0(sK3)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2540,c_26,c_27,c_28,c_29,c_30])).

cnf(c_2546,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2545])).

cnf(c_2554,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2546,c_701])).

cnf(c_2558,plain,
    ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)))
    | k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_681,c_2554])).

cnf(c_17,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_670,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_684,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_892,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_670,c_684])).

cnf(c_4399,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | r2_orders_2(sK3,X0,sK0(k1_orders_2(sK3,k2_struct_0(sK3)))) = iProver_top
    | r2_hidden(X0,k2_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2558,c_892])).

cnf(c_4478,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | r2_orders_2(sK3,X0,sK0(k1_orders_2(sK3,k2_struct_0(sK3)))) = iProver_top
    | r2_hidden(X0,k2_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4399,c_1411,c_2418])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_974,plain,
    ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
    | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_975,plain,
    ( k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_974])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_675,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3080,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_675])).

cnf(c_3137,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3080,c_1411])).

cnf(c_3703,plain,
    ( m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3137,c_26,c_27,c_28,c_29,c_30])).

cnf(c_3704,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3703])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_685,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3711,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3704,c_685])).

cnf(c_4035,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_3711])).

cnf(c_4628,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_681,c_4035])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_668,plain,
    ( r2_hidden(X0,a_2_0_orders_2(X1,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1506,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_668])).

cnf(c_1507,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1506,c_1411])).

cnf(c_1512,plain,
    ( m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1507,c_26,c_27,c_28,c_29,c_30])).

cnf(c_1513,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1512])).

cnf(c_9,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_678,plain,
    ( r2_orders_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1885,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_678])).

cnf(c_2236,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | r2_orders_2(sK3,X0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1885,c_30])).

cnf(c_2237,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2236])).

cnf(c_2244,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),sK2(X0,sK3,X1)) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1513,c_2237])).

cnf(c_4401,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_892,c_2244])).

cnf(c_4437,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4401,c_1411])).

cnf(c_4864,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4437,c_26,c_27,c_28,c_29,c_30])).

cnf(c_4865,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4864])).

cnf(c_4873,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2558,c_4865])).

cnf(c_4874,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4873,c_2418])).

cnf(c_5333,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4478,c_20,c_975,c_4628,c_4874])).

cnf(c_5334,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5333])).

cnf(c_5339,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5334,c_701])).

cnf(c_5349,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5339,c_20])).

cnf(c_5350,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_5349])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:59:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.75/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.02  
% 3.75/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.75/1.02  
% 3.75/1.02  ------  iProver source info
% 3.75/1.02  
% 3.75/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.75/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.75/1.02  git: non_committed_changes: false
% 3.75/1.02  git: last_make_outside_of_git: false
% 3.75/1.02  
% 3.75/1.02  ------ 
% 3.75/1.02  ------ Parsing...
% 3.75/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.75/1.02  
% 3.75/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.75/1.02  
% 3.75/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.75/1.02  
% 3.75/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/1.02  ------ Proving...
% 3.75/1.02  ------ Problem Properties 
% 3.75/1.02  
% 3.75/1.02  
% 3.75/1.02  clauses                                 26
% 3.75/1.02  conjectures                             6
% 3.75/1.02  EPR                                     6
% 3.75/1.02  Horn                                    16
% 3.75/1.02  unary                                   8
% 3.75/1.02  binary                                  3
% 3.75/1.02  lits                                    107
% 3.75/1.02  lits eq                                 11
% 3.75/1.02  fd_pure                                 0
% 3.75/1.02  fd_pseudo                               0
% 3.75/1.02  fd_cond                                 3
% 3.75/1.02  fd_pseudo_cond                          1
% 3.75/1.02  AC symbols                              0
% 3.75/1.02  
% 3.75/1.02  ------ Input Options Time Limit: Unbounded
% 3.75/1.02  
% 3.75/1.02  
% 3.75/1.02  ------ 
% 3.75/1.02  Current options:
% 3.75/1.02  ------ 
% 3.75/1.02  
% 3.75/1.02  
% 3.75/1.02  
% 3.75/1.02  
% 3.75/1.02  ------ Proving...
% 3.75/1.02  
% 3.75/1.02  
% 3.75/1.02  % SZS status Theorem for theBenchmark.p
% 3.75/1.02  
% 3.75/1.02   Resolution empty clause
% 3.75/1.02  
% 3.75/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.75/1.02  
% 3.75/1.02  fof(f5,axiom,(
% 3.75/1.02    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.75/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/1.02  
% 3.75/1.02  fof(f17,plain,(
% 3.75/1.02    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.75/1.02    inference(ennf_transformation,[],[f5])).
% 3.75/1.02  
% 3.75/1.02  fof(f29,plain,(
% 3.75/1.02    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 3.75/1.02    introduced(choice_axiom,[])).
% 3.75/1.02  
% 3.75/1.02  fof(f30,plain,(
% 3.75/1.02    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 3.75/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f29])).
% 3.75/1.02  
% 3.75/1.02  fof(f44,plain,(
% 3.75/1.02    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.75/1.02    inference(cnf_transformation,[],[f30])).
% 3.75/1.02  
% 3.75/1.02  fof(f2,axiom,(
% 3.75/1.02    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.75/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/1.02  
% 3.75/1.02  fof(f41,plain,(
% 3.75/1.02    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.75/1.02    inference(cnf_transformation,[],[f2])).
% 3.75/1.02  
% 3.75/1.02  fof(f1,axiom,(
% 3.75/1.02    ! [X0] : k2_subset_1(X0) = X0),
% 3.75/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/1.02  
% 3.75/1.02  fof(f40,plain,(
% 3.75/1.02    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.75/1.02    inference(cnf_transformation,[],[f1])).
% 3.75/1.02  
% 3.75/1.02  fof(f12,conjecture,(
% 3.75/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 3.75/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/1.02  
% 3.75/1.02  fof(f13,negated_conjecture,(
% 3.75/1.02    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 3.75/1.02    inference(negated_conjecture,[],[f12])).
% 3.75/1.02  
% 3.75/1.02  fof(f27,plain,(
% 3.75/1.02    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.75/1.02    inference(ennf_transformation,[],[f13])).
% 3.75/1.02  
% 3.75/1.02  fof(f28,plain,(
% 3.75/1.02    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.75/1.02    inference(flattening,[],[f27])).
% 3.75/1.02  
% 3.75/1.02  fof(f38,plain,(
% 3.75/1.02    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 3.75/1.02    introduced(choice_axiom,[])).
% 3.75/1.02  
% 3.75/1.02  fof(f39,plain,(
% 3.75/1.02    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 3.75/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f38])).
% 3.75/1.02  
% 3.75/1.02  fof(f64,plain,(
% 3.75/1.02    l1_orders_2(sK3)),
% 3.75/1.02    inference(cnf_transformation,[],[f39])).
% 3.75/1.02  
% 3.75/1.02  fof(f10,axiom,(
% 3.75/1.02    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.75/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/1.02  
% 3.75/1.02  fof(f24,plain,(
% 3.75/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.75/1.02    inference(ennf_transformation,[],[f10])).
% 3.75/1.02  
% 3.75/1.02  fof(f53,plain,(
% 3.75/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.75/1.02    inference(cnf_transformation,[],[f24])).
% 3.75/1.02  
% 3.75/1.02  fof(f6,axiom,(
% 3.75/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.75/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/1.02  
% 3.75/1.02  fof(f18,plain,(
% 3.75/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.75/1.02    inference(ennf_transformation,[],[f6])).
% 3.75/1.02  
% 3.75/1.02  fof(f47,plain,(
% 3.75/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.75/1.02    inference(cnf_transformation,[],[f18])).
% 3.75/1.02  
% 3.75/1.02  fof(f8,axiom,(
% 3.75/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 3.75/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/1.02  
% 3.75/1.02  fof(f20,plain,(
% 3.75/1.02    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.75/1.02    inference(ennf_transformation,[],[f8])).
% 3.75/1.02  
% 3.75/1.02  fof(f21,plain,(
% 3.75/1.02    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.75/1.02    inference(flattening,[],[f20])).
% 3.75/1.02  
% 3.75/1.02  fof(f51,plain,(
% 3.75/1.02    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.75/1.02    inference(cnf_transformation,[],[f21])).
% 3.75/1.02  
% 3.75/1.02  fof(f60,plain,(
% 3.75/1.02    ~v2_struct_0(sK3)),
% 3.75/1.02    inference(cnf_transformation,[],[f39])).
% 3.75/1.02  
% 3.75/1.02  fof(f61,plain,(
% 3.75/1.02    v3_orders_2(sK3)),
% 3.75/1.02    inference(cnf_transformation,[],[f39])).
% 3.75/1.02  
% 3.75/1.02  fof(f62,plain,(
% 3.75/1.02    v4_orders_2(sK3)),
% 3.75/1.02    inference(cnf_transformation,[],[f39])).
% 3.75/1.02  
% 3.75/1.02  fof(f63,plain,(
% 3.75/1.02    v5_orders_2(sK3)),
% 3.75/1.02    inference(cnf_transformation,[],[f39])).
% 3.75/1.02  
% 3.75/1.02  fof(f11,axiom,(
% 3.75/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.75/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/1.02  
% 3.75/1.02  fof(f25,plain,(
% 3.75/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 3.75/1.02    inference(ennf_transformation,[],[f11])).
% 3.75/1.02  
% 3.75/1.02  fof(f26,plain,(
% 3.75/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.75/1.02    inference(flattening,[],[f25])).
% 3.75/1.02  
% 3.75/1.02  fof(f33,plain,(
% 3.75/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.75/1.02    inference(nnf_transformation,[],[f26])).
% 3.75/1.02  
% 3.75/1.02  fof(f34,plain,(
% 3.75/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.75/1.02    inference(rectify,[],[f33])).
% 3.75/1.02  
% 3.75/1.02  fof(f36,plain,(
% 3.75/1.02    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.75/1.02    introduced(choice_axiom,[])).
% 3.75/1.02  
% 3.75/1.02  fof(f35,plain,(
% 3.75/1.02    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 3.75/1.02    introduced(choice_axiom,[])).
% 3.75/1.02  
% 3.75/1.02  fof(f37,plain,(
% 3.75/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.75/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).
% 3.75/1.02  
% 3.75/1.02  fof(f55,plain,(
% 3.75/1.02    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.75/1.02    inference(cnf_transformation,[],[f37])).
% 3.75/1.02  
% 3.75/1.02  fof(f56,plain,(
% 3.75/1.02    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.75/1.02    inference(cnf_transformation,[],[f37])).
% 3.75/1.02  
% 3.75/1.02  fof(f4,axiom,(
% 3.75/1.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.75/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/1.02  
% 3.75/1.02  fof(f15,plain,(
% 3.75/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.75/1.02    inference(ennf_transformation,[],[f4])).
% 3.75/1.02  
% 3.75/1.02  fof(f16,plain,(
% 3.75/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.75/1.02    inference(flattening,[],[f15])).
% 3.75/1.02  
% 3.75/1.02  fof(f43,plain,(
% 3.75/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.75/1.02    inference(cnf_transformation,[],[f16])).
% 3.75/1.02  
% 3.75/1.02  fof(f65,plain,(
% 3.75/1.02    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))),
% 3.75/1.02    inference(cnf_transformation,[],[f39])).
% 3.75/1.02  
% 3.75/1.02  fof(f9,axiom,(
% 3.75/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.75/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/1.02  
% 3.75/1.02  fof(f22,plain,(
% 3.75/1.02    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.75/1.02    inference(ennf_transformation,[],[f9])).
% 3.75/1.02  
% 3.75/1.02  fof(f23,plain,(
% 3.75/1.02    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.75/1.02    inference(flattening,[],[f22])).
% 3.75/1.02  
% 3.75/1.02  fof(f52,plain,(
% 3.75/1.02    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.75/1.02    inference(cnf_transformation,[],[f23])).
% 3.75/1.02  
% 3.75/1.02  fof(f3,axiom,(
% 3.75/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.75/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/1.02  
% 3.75/1.02  fof(f14,plain,(
% 3.75/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.75/1.02    inference(ennf_transformation,[],[f3])).
% 3.75/1.02  
% 3.75/1.02  fof(f42,plain,(
% 3.75/1.02    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.75/1.02    inference(cnf_transformation,[],[f14])).
% 3.75/1.02  
% 3.75/1.02  fof(f54,plain,(
% 3.75/1.02    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.75/1.02    inference(cnf_transformation,[],[f37])).
% 3.75/1.02  
% 3.75/1.02  fof(f7,axiom,(
% 3.75/1.02    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 3.75/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/1.02  
% 3.75/1.02  fof(f19,plain,(
% 3.75/1.02    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.75/1.02    inference(ennf_transformation,[],[f7])).
% 3.75/1.02  
% 3.75/1.02  fof(f31,plain,(
% 3.75/1.02    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.75/1.02    inference(nnf_transformation,[],[f19])).
% 3.75/1.02  
% 3.75/1.02  fof(f32,plain,(
% 3.75/1.02    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.75/1.02    inference(flattening,[],[f31])).
% 3.75/1.02  
% 3.75/1.02  fof(f49,plain,(
% 3.75/1.02    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.75/1.02    inference(cnf_transformation,[],[f32])).
% 3.75/1.02  
% 3.75/1.02  fof(f66,plain,(
% 3.75/1.02    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.75/1.02    inference(equality_resolution,[],[f49])).
% 3.75/1.02  
% 3.75/1.02  cnf(c_6,plain,
% 3.75/1.02      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.75/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_681,plain,
% 3.75/1.02      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_1,plain,
% 3.75/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.75/1.02      inference(cnf_transformation,[],[f41]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_686,plain,
% 3.75/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_0,plain,
% 3.75/1.02      ( k2_subset_1(X0) = X0 ),
% 3.75/1.02      inference(cnf_transformation,[],[f40]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_701,plain,
% 3.75/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.75/1.02      inference(light_normalisation,[status(thm)],[c_686,c_0]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_21,negated_conjecture,
% 3.75/1.02      ( l1_orders_2(sK3) ),
% 3.75/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_667,plain,
% 3.75/1.02      ( l1_orders_2(sK3) = iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_13,plain,
% 3.75/1.02      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.75/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_674,plain,
% 3.75/1.02      ( l1_orders_2(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_1172,plain,
% 3.75/1.02      ( l1_struct_0(sK3) = iProver_top ),
% 3.75/1.02      inference(superposition,[status(thm)],[c_667,c_674]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_7,plain,
% 3.75/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.75/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_680,plain,
% 3.75/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | l1_struct_0(X0) != iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_1411,plain,
% 3.75/1.02      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.75/1.02      inference(superposition,[status(thm)],[c_1172,c_680]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_11,plain,
% 3.75/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.75/1.02      | v2_struct_0(X1)
% 3.75/1.02      | ~ v3_orders_2(X1)
% 3.75/1.02      | ~ v4_orders_2(X1)
% 3.75/1.02      | ~ v5_orders_2(X1)
% 3.75/1.02      | ~ l1_orders_2(X1)
% 3.75/1.02      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 3.75/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_676,plain,
% 3.75/1.02      ( a_2_0_orders_2(X0,X1) = k1_orders_2(X0,X1)
% 3.75/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.75/1.02      | v2_struct_0(X0) = iProver_top
% 3.75/1.02      | v3_orders_2(X0) != iProver_top
% 3.75/1.02      | v4_orders_2(X0) != iProver_top
% 3.75/1.02      | v5_orders_2(X0) != iProver_top
% 3.75/1.02      | l1_orders_2(X0) != iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_2202,plain,
% 3.75/1.02      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 3.75/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | v2_struct_0(sK3) = iProver_top
% 3.75/1.02      | v3_orders_2(sK3) != iProver_top
% 3.75/1.02      | v4_orders_2(sK3) != iProver_top
% 3.75/1.02      | v5_orders_2(sK3) != iProver_top
% 3.75/1.02      | l1_orders_2(sK3) != iProver_top ),
% 3.75/1.02      inference(superposition,[status(thm)],[c_1411,c_676]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_25,negated_conjecture,
% 3.75/1.02      ( ~ v2_struct_0(sK3) ),
% 3.75/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_26,plain,
% 3.75/1.02      ( v2_struct_0(sK3) != iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_24,negated_conjecture,
% 3.75/1.02      ( v3_orders_2(sK3) ),
% 3.75/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_27,plain,
% 3.75/1.02      ( v3_orders_2(sK3) = iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_23,negated_conjecture,
% 3.75/1.02      ( v4_orders_2(sK3) ),
% 3.75/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_28,plain,
% 3.75/1.02      ( v4_orders_2(sK3) = iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_22,negated_conjecture,
% 3.75/1.02      ( v5_orders_2(sK3) ),
% 3.75/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_29,plain,
% 3.75/1.02      ( v5_orders_2(sK3) = iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_30,plain,
% 3.75/1.02      ( l1_orders_2(sK3) = iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_2410,plain,
% 3.75/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 3.75/1.02      inference(global_propositional_subsumption,
% 3.75/1.02                [status(thm)],
% 3.75/1.02                [c_2202,c_26,c_27,c_28,c_29,c_30]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_2411,plain,
% 3.75/1.02      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 3.75/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.75/1.02      inference(renaming,[status(thm)],[c_2410]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_2418,plain,
% 3.75/1.02      ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.75/1.02      inference(superposition,[status(thm)],[c_701,c_2411]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_18,plain,
% 3.75/1.02      ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 3.75/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.75/1.02      | v2_struct_0(X1)
% 3.75/1.02      | ~ v3_orders_2(X1)
% 3.75/1.02      | ~ v4_orders_2(X1)
% 3.75/1.02      | ~ v5_orders_2(X1)
% 3.75/1.02      | ~ l1_orders_2(X1)
% 3.75/1.02      | sK2(X0,X1,X2) = X0 ),
% 3.75/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_669,plain,
% 3.75/1.02      ( sK2(X0,X1,X2) = X0
% 3.75/1.02      | r2_hidden(X0,a_2_0_orders_2(X1,X2)) != iProver_top
% 3.75/1.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.75/1.02      | v2_struct_0(X1) = iProver_top
% 3.75/1.02      | v3_orders_2(X1) != iProver_top
% 3.75/1.02      | v4_orders_2(X1) != iProver_top
% 3.75/1.02      | v5_orders_2(X1) != iProver_top
% 3.75/1.02      | l1_orders_2(X1) != iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_2539,plain,
% 3.75/1.02      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 3.75/1.02      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.75/1.02      | v2_struct_0(sK3) = iProver_top
% 3.75/1.02      | v3_orders_2(sK3) != iProver_top
% 3.75/1.02      | v4_orders_2(sK3) != iProver_top
% 3.75/1.02      | v5_orders_2(sK3) != iProver_top
% 3.75/1.02      | l1_orders_2(sK3) != iProver_top ),
% 3.75/1.02      inference(superposition,[status(thm)],[c_2418,c_669]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_2540,plain,
% 3.75/1.02      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 3.75/1.02      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | v2_struct_0(sK3) = iProver_top
% 3.75/1.02      | v3_orders_2(sK3) != iProver_top
% 3.75/1.02      | v4_orders_2(sK3) != iProver_top
% 3.75/1.02      | v5_orders_2(sK3) != iProver_top
% 3.75/1.02      | l1_orders_2(sK3) != iProver_top ),
% 3.75/1.02      inference(light_normalisation,[status(thm)],[c_2539,c_1411]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_2545,plain,
% 3.75/1.02      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | sK2(X0,sK3,k2_struct_0(sK3)) = X0 ),
% 3.75/1.02      inference(global_propositional_subsumption,
% 3.75/1.02                [status(thm)],
% 3.75/1.02                [c_2540,c_26,c_27,c_28,c_29,c_30]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_2546,plain,
% 3.75/1.02      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 3.75/1.02      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.75/1.02      inference(renaming,[status(thm)],[c_2545]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_2554,plain,
% 3.75/1.02      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 3.75/1.02      | r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 3.75/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_2546,c_701]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_2558,plain,
% 3.75/1.02      ( sK2(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k1_orders_2(sK3,k2_struct_0(sK3)))
% 3.75/1.02      | k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 3.75/1.02      inference(superposition,[status(thm)],[c_681,c_2554]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_17,plain,
% 3.75/1.02      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 3.75/1.02      | ~ r2_hidden(X1,X3)
% 3.75/1.02      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 3.75/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.75/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.75/1.02      | v2_struct_0(X0)
% 3.75/1.02      | ~ v3_orders_2(X0)
% 3.75/1.02      | ~ v4_orders_2(X0)
% 3.75/1.02      | ~ v5_orders_2(X0)
% 3.75/1.02      | ~ l1_orders_2(X0) ),
% 3.75/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_670,plain,
% 3.75/1.02      ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
% 3.75/1.02      | r2_hidden(X1,X3) != iProver_top
% 3.75/1.02      | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
% 3.75/1.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.75/1.02      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.75/1.02      | v2_struct_0(X0) = iProver_top
% 3.75/1.02      | v3_orders_2(X0) != iProver_top
% 3.75/1.02      | v4_orders_2(X0) != iProver_top
% 3.75/1.02      | v5_orders_2(X0) != iProver_top
% 3.75/1.02      | l1_orders_2(X0) != iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_3,plain,
% 3.75/1.02      ( ~ r2_hidden(X0,X1)
% 3.75/1.02      | m1_subset_1(X0,X2)
% 3.75/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.75/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_684,plain,
% 3.75/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.75/1.02      | m1_subset_1(X0,X2) = iProver_top
% 3.75/1.02      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_892,plain,
% 3.75/1.02      ( r2_orders_2(X0,X1,sK2(X2,X0,X3)) = iProver_top
% 3.75/1.02      | r2_hidden(X1,X3) != iProver_top
% 3.75/1.02      | r2_hidden(X2,a_2_0_orders_2(X0,X3)) != iProver_top
% 3.75/1.02      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.75/1.02      | v2_struct_0(X0) = iProver_top
% 3.75/1.02      | v3_orders_2(X0) != iProver_top
% 3.75/1.02      | v4_orders_2(X0) != iProver_top
% 3.75/1.02      | v5_orders_2(X0) != iProver_top
% 3.75/1.02      | l1_orders_2(X0) != iProver_top ),
% 3.75/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_670,c_684]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_4399,plain,
% 3.75/1.02      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 3.75/1.02      | r2_orders_2(sK3,X0,sK0(k1_orders_2(sK3,k2_struct_0(sK3)))) = iProver_top
% 3.75/1.02      | r2_hidden(X0,k2_struct_0(sK3)) != iProver_top
% 3.75/1.02      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.75/1.02      | v2_struct_0(sK3) = iProver_top
% 3.75/1.02      | v3_orders_2(sK3) != iProver_top
% 3.75/1.02      | v4_orders_2(sK3) != iProver_top
% 3.75/1.02      | v5_orders_2(sK3) != iProver_top
% 3.75/1.02      | l1_orders_2(sK3) != iProver_top ),
% 3.75/1.02      inference(superposition,[status(thm)],[c_2558,c_892]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_4478,plain,
% 3.75/1.02      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 3.75/1.02      | r2_orders_2(sK3,X0,sK0(k1_orders_2(sK3,k2_struct_0(sK3)))) = iProver_top
% 3.75/1.02      | r2_hidden(X0,k2_struct_0(sK3)) != iProver_top
% 3.75/1.02      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | v2_struct_0(sK3) = iProver_top
% 3.75/1.02      | v3_orders_2(sK3) != iProver_top
% 3.75/1.02      | v4_orders_2(sK3) != iProver_top
% 3.75/1.02      | v5_orders_2(sK3) != iProver_top
% 3.75/1.02      | l1_orders_2(sK3) != iProver_top ),
% 3.75/1.02      inference(light_normalisation,[status(thm)],[c_4399,c_1411,c_2418]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_20,negated_conjecture,
% 3.75/1.02      ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.75/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_974,plain,
% 3.75/1.02      ( r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3)))
% 3.75/1.02      | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 3.75/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_975,plain,
% 3.75/1.02      ( k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
% 3.75/1.02      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) = iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_974]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_12,plain,
% 3.75/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.75/1.02      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.75/1.02      | v2_struct_0(X1)
% 3.75/1.02      | ~ v3_orders_2(X1)
% 3.75/1.02      | ~ v4_orders_2(X1)
% 3.75/1.02      | ~ v5_orders_2(X1)
% 3.75/1.02      | ~ l1_orders_2(X1) ),
% 3.75/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_675,plain,
% 3.75/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.75/1.02      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.75/1.02      | v2_struct_0(X1) = iProver_top
% 3.75/1.02      | v3_orders_2(X1) != iProver_top
% 3.75/1.02      | v4_orders_2(X1) != iProver_top
% 3.75/1.02      | v5_orders_2(X1) != iProver_top
% 3.75/1.02      | l1_orders_2(X1) != iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_3080,plain,
% 3.75/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.75/1.02      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.75/1.02      | v2_struct_0(sK3) = iProver_top
% 3.75/1.02      | v3_orders_2(sK3) != iProver_top
% 3.75/1.02      | v4_orders_2(sK3) != iProver_top
% 3.75/1.02      | v5_orders_2(sK3) != iProver_top
% 3.75/1.02      | l1_orders_2(sK3) != iProver_top ),
% 3.75/1.02      inference(superposition,[status(thm)],[c_1411,c_675]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_3137,plain,
% 3.75/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.75/1.02      | v2_struct_0(sK3) = iProver_top
% 3.75/1.02      | v3_orders_2(sK3) != iProver_top
% 3.75/1.02      | v4_orders_2(sK3) != iProver_top
% 3.75/1.02      | v5_orders_2(sK3) != iProver_top
% 3.75/1.02      | l1_orders_2(sK3) != iProver_top ),
% 3.75/1.02      inference(light_normalisation,[status(thm)],[c_3080,c_1411]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_3703,plain,
% 3.75/1.02      ( m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.75/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.75/1.02      inference(global_propositional_subsumption,
% 3.75/1.02                [status(thm)],
% 3.75/1.02                [c_3137,c_26,c_27,c_28,c_29,c_30]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_3704,plain,
% 3.75/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 3.75/1.02      inference(renaming,[status(thm)],[c_3703]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_2,plain,
% 3.75/1.02      ( ~ r2_hidden(X0,X1)
% 3.75/1.02      | r2_hidden(X0,X2)
% 3.75/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.75/1.02      inference(cnf_transformation,[],[f42]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_685,plain,
% 3.75/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.75/1.02      | r2_hidden(X0,X2) = iProver_top
% 3.75/1.02      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_3711,plain,
% 3.75/1.02      ( r2_hidden(X0,k1_orders_2(sK3,X1)) != iProver_top
% 3.75/1.02      | r2_hidden(X0,k2_struct_0(sK3)) = iProver_top
% 3.75/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.75/1.02      inference(superposition,[status(thm)],[c_3704,c_685]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_4035,plain,
% 3.75/1.02      ( r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | r2_hidden(X0,k2_struct_0(sK3)) = iProver_top ),
% 3.75/1.02      inference(superposition,[status(thm)],[c_701,c_3711]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_4628,plain,
% 3.75/1.02      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 3.75/1.02      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
% 3.75/1.02      inference(superposition,[status(thm)],[c_681,c_4035]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_19,plain,
% 3.75/1.02      ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 3.75/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.75/1.02      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 3.75/1.02      | v2_struct_0(X1)
% 3.75/1.02      | ~ v3_orders_2(X1)
% 3.75/1.02      | ~ v4_orders_2(X1)
% 3.75/1.02      | ~ v5_orders_2(X1)
% 3.75/1.02      | ~ l1_orders_2(X1) ),
% 3.75/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_668,plain,
% 3.75/1.02      ( r2_hidden(X0,a_2_0_orders_2(X1,X2)) != iProver_top
% 3.75/1.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.75/1.02      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top
% 3.75/1.02      | v2_struct_0(X1) = iProver_top
% 3.75/1.02      | v3_orders_2(X1) != iProver_top
% 3.75/1.02      | v4_orders_2(X1) != iProver_top
% 3.75/1.02      | v5_orders_2(X1) != iProver_top
% 3.75/1.02      | l1_orders_2(X1) != iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_1506,plain,
% 3.75/1.02      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 3.75/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.75/1.02      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
% 3.75/1.02      | v2_struct_0(sK3) = iProver_top
% 3.75/1.02      | v3_orders_2(sK3) != iProver_top
% 3.75/1.02      | v4_orders_2(sK3) != iProver_top
% 3.75/1.02      | v5_orders_2(sK3) != iProver_top
% 3.75/1.02      | l1_orders_2(sK3) != iProver_top ),
% 3.75/1.02      inference(superposition,[status(thm)],[c_1411,c_668]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_1507,plain,
% 3.75/1.02      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 3.75/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
% 3.75/1.02      | v2_struct_0(sK3) = iProver_top
% 3.75/1.02      | v3_orders_2(sK3) != iProver_top
% 3.75/1.02      | v4_orders_2(sK3) != iProver_top
% 3.75/1.02      | v5_orders_2(sK3) != iProver_top
% 3.75/1.02      | l1_orders_2(sK3) != iProver_top ),
% 3.75/1.02      inference(light_normalisation,[status(thm)],[c_1506,c_1411]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_1512,plain,
% 3.75/1.02      ( m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
% 3.75/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
% 3.75/1.02      inference(global_propositional_subsumption,
% 3.75/1.02                [status(thm)],
% 3.75/1.02                [c_1507,c_26,c_27,c_28,c_29,c_30]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_1513,plain,
% 3.75/1.02      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 3.75/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top ),
% 3.75/1.02      inference(renaming,[status(thm)],[c_1512]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_9,plain,
% 3.75/1.02      ( ~ r2_orders_2(X0,X1,X1)
% 3.75/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.75/1.02      | ~ l1_orders_2(X0) ),
% 3.75/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_678,plain,
% 3.75/1.02      ( r2_orders_2(X0,X1,X1) != iProver_top
% 3.75/1.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.75/1.02      | l1_orders_2(X0) != iProver_top ),
% 3.75/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_1885,plain,
% 3.75/1.02      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 3.75/1.02      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.75/1.02      | l1_orders_2(sK3) != iProver_top ),
% 3.75/1.02      inference(superposition,[status(thm)],[c_1411,c_678]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_2236,plain,
% 3.75/1.02      ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 3.75/1.02      | r2_orders_2(sK3,X0,X0) != iProver_top ),
% 3.75/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1885,c_30]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_2237,plain,
% 3.75/1.02      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 3.75/1.02      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 3.75/1.02      inference(renaming,[status(thm)],[c_2236]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_2244,plain,
% 3.75/1.02      ( r2_orders_2(sK3,sK2(X0,sK3,X1),sK2(X0,sK3,X1)) != iProver_top
% 3.75/1.02      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 3.75/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.75/1.02      inference(superposition,[status(thm)],[c_1513,c_2237]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_4401,plain,
% 3.75/1.02      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 3.75/1.02      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 3.75/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.75/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | v2_struct_0(sK3) = iProver_top
% 3.75/1.02      | v3_orders_2(sK3) != iProver_top
% 3.75/1.02      | v4_orders_2(sK3) != iProver_top
% 3.75/1.02      | v5_orders_2(sK3) != iProver_top
% 3.75/1.02      | l1_orders_2(sK3) != iProver_top ),
% 3.75/1.02      inference(superposition,[status(thm)],[c_892,c_2244]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_4437,plain,
% 3.75/1.02      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 3.75/1.02      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 3.75/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | v2_struct_0(sK3) = iProver_top
% 3.75/1.02      | v3_orders_2(sK3) != iProver_top
% 3.75/1.02      | v4_orders_2(sK3) != iProver_top
% 3.75/1.02      | v5_orders_2(sK3) != iProver_top
% 3.75/1.02      | l1_orders_2(sK3) != iProver_top ),
% 3.75/1.02      inference(light_normalisation,[status(thm)],[c_4401,c_1411]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_4864,plain,
% 3.75/1.02      ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 3.75/1.02      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
% 3.75/1.02      inference(global_propositional_subsumption,
% 3.75/1.02                [status(thm)],
% 3.75/1.02                [c_4437,c_26,c_27,c_28,c_29,c_30]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_4865,plain,
% 3.75/1.02      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 3.75/1.02      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 3.75/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.75/1.02      inference(renaming,[status(thm)],[c_4864]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_4873,plain,
% 3.75/1.02      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 3.75/1.02      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top
% 3.75/1.02      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.75/1.02      inference(superposition,[status(thm)],[c_2558,c_4865]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_4874,plain,
% 3.75/1.02      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 3.75/1.02      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | r2_hidden(sK0(k1_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top
% 3.75/1.02      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.75/1.02      inference(light_normalisation,[status(thm)],[c_4873,c_2418]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_5333,plain,
% 3.75/1.02      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.75/1.02      | k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 3.75/1.02      inference(global_propositional_subsumption,
% 3.75/1.02                [status(thm)],
% 3.75/1.02                [c_4478,c_20,c_975,c_4628,c_4874]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_5334,plain,
% 3.75/1.02      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 3.75/1.02      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 3.75/1.02      inference(renaming,[status(thm)],[c_5333]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_5339,plain,
% 3.75/1.02      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 3.75/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_5334,c_701]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_5349,plain,
% 3.75/1.02      ( k1_xboole_0 != k1_xboole_0 ),
% 3.75/1.02      inference(demodulation,[status(thm)],[c_5339,c_20]) ).
% 3.75/1.02  
% 3.75/1.02  cnf(c_5350,plain,
% 3.75/1.02      ( $false ),
% 3.75/1.02      inference(equality_resolution_simp,[status(thm)],[c_5349]) ).
% 3.75/1.02  
% 3.75/1.02  
% 3.75/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.75/1.02  
% 3.75/1.02  ------                               Statistics
% 3.75/1.02  
% 3.75/1.02  ------ Selected
% 3.75/1.02  
% 3.75/1.02  total_time:                             0.224
% 3.75/1.02  
%------------------------------------------------------------------------------
