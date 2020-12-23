%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:06 EST 2020

% Result     : Theorem 39.42s
% Output     : CNFRefutation 39.42s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 738 expanded)
%              Number of clauses        :  115 ( 255 expanded)
%              Number of leaves         :   24 ( 173 expanded)
%              Depth                    :   18
%              Number of atoms          :  742 (3509 expanded)
%              Number of equality atoms :  165 ( 644 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f30,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

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
   => ( k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4))
      & l1_orders_2(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4))
    & l1_orders_2(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f46])).

fof(f77,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f37])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

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

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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
            ( r2_orders_2(X1,X6,sK3(X0,X1,X2))
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK2(X1,X2,X3),X3)
        & r2_hidden(sK2(X1,X2,X3),X2)
        & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f44,f43])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1324,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1323,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_6140,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_1324,c_1323])).

cnf(c_18,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_12,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_411,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_18,c_12])).

cnf(c_26,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_877,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_411,c_26])).

cnf(c_878,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_877])).

cnf(c_17030,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK4)))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_6140,c_878])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_17631,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,k2_struct_0(sK4))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_17030,c_5])).

cnf(c_1320,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_3927,plain,
    ( X0 = u1_struct_0(sK4)
    | X0 != k2_struct_0(sK4) ),
    inference(resolution,[status(thm)],[c_1320,c_878])).

cnf(c_33886,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(u1_struct_0(sK4),k2_struct_0(sK4))
    | X0 != k2_struct_0(sK4) ),
    inference(resolution,[status(thm)],[c_17631,c_3927])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_55,plain,
    ( ~ l1_orders_2(sK4)
    | l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_73,plain,
    ( ~ l1_struct_0(sK4)
    | u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1325,plain,
    ( X0 != X1
    | k2_struct_0(X0) = k2_struct_0(X1) ),
    theory(equality)).

cnf(c_1336,plain,
    ( k2_struct_0(sK4) = k2_struct_0(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_1326,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1337,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_1319,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1344,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1319])).

cnf(c_11,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1979,plain,
    ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
    | k1_xboole_0 = k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2302,plain,
    ( k1_orders_2(sK4,k2_struct_0(sK4)) = k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1319])).

cnf(c_2948,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(c_2311,plain,
    ( X0 != X1
    | k2_struct_0(sK4) != X1
    | k2_struct_0(sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_1320])).

cnf(c_3069,plain,
    ( X0 != k2_struct_0(sK4)
    | k2_struct_0(sK4) = X0
    | k2_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2311])).

cnf(c_1328,plain,
    ( X0 != X1
    | X2 != X3
    | k1_orders_2(X0,X2) = k1_orders_2(X1,X3) ),
    theory(equality)).

cnf(c_2796,plain,
    ( X0 != k2_struct_0(sK4)
    | X1 != sK4
    | k1_orders_2(X1,X0) = k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1328])).

cnf(c_3460,plain,
    ( X0 != sK4
    | k1_orders_2(X0,u1_struct_0(sK4)) = k1_orders_2(sK4,k2_struct_0(sK4))
    | u1_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2796])).

cnf(c_3461,plain,
    ( k1_orders_2(sK4,u1_struct_0(sK4)) = k1_orders_2(sK4,k2_struct_0(sK4))
    | u1_struct_0(sK4) != k2_struct_0(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3460])).

cnf(c_2093,plain,
    ( X0 != X1
    | k1_orders_2(sK4,k2_struct_0(sK4)) != X1
    | k1_orders_2(sK4,k2_struct_0(sK4)) = X0 ),
    inference(instantiation,[status(thm)],[c_1320])).

cnf(c_2301,plain,
    ( X0 != k1_orders_2(sK4,k2_struct_0(sK4))
    | k1_orders_2(sK4,k2_struct_0(sK4)) = X0
    | k1_orders_2(sK4,k2_struct_0(sK4)) != k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2093])).

cnf(c_3791,plain,
    ( k1_orders_2(X0,u1_struct_0(sK4)) != k1_orders_2(sK4,k2_struct_0(sK4))
    | k1_orders_2(sK4,k2_struct_0(sK4)) = k1_orders_2(X0,u1_struct_0(sK4))
    | k1_orders_2(sK4,k2_struct_0(sK4)) != k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2301])).

cnf(c_3793,plain,
    ( k1_orders_2(sK4,u1_struct_0(sK4)) != k1_orders_2(sK4,k2_struct_0(sK4))
    | k1_orders_2(sK4,k2_struct_0(sK4)) = k1_orders_2(sK4,u1_struct_0(sK4))
    | k1_orders_2(sK4,k2_struct_0(sK4)) != k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3791])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_807,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_808,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_807])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_29,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_28,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_812,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_808,c_30,c_29,c_28,c_26])).

cnf(c_4560,plain,
    ( m1_subset_1(k1_orders_2(sK4,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_5098,plain,
    ( u1_struct_0(sK4) != k2_struct_0(sK4)
    | k2_struct_0(sK4) = u1_struct_0(sK4)
    | k2_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3069])).

cnf(c_2019,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1324])).

cnf(c_2164,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2019])).

cnf(c_2603,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | k2_struct_0(sK4) != X0
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2164])).

cnf(c_7038,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | k2_struct_0(sK4) != u1_struct_0(sK4)
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2603])).

cnf(c_2171,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2019])).

cnf(c_2593,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X2))
    | k1_orders_2(sK4,k2_struct_0(sK4)) != X0
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2171])).

cnf(c_3199,plain,
    ( ~ m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X0))
    | m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X1))
    | k1_orders_2(sK4,k2_struct_0(sK4)) != k1_orders_2(sK4,k2_struct_0(sK4))
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_2593])).

cnf(c_11898,plain,
    ( ~ m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X0))
    | m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(k2_struct_0(sK4)))
    | k1_orders_2(sK4,k2_struct_0(sK4)) != k1_orders_2(sK4,k2_struct_0(sK4))
    | k1_zfmisc_1(k2_struct_0(sK4)) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_3199])).

cnf(c_4573,plain,
    ( ~ m1_subset_1(k1_orders_2(X0,u1_struct_0(sK4)),k1_zfmisc_1(X1))
    | m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X2))
    | k1_orders_2(sK4,k2_struct_0(sK4)) != k1_orders_2(X0,u1_struct_0(sK4))
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2593])).

cnf(c_12532,plain,
    ( ~ m1_subset_1(k1_orders_2(sK4,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X0))
    | k1_orders_2(sK4,k2_struct_0(sK4)) != k1_orders_2(sK4,u1_struct_0(sK4))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4573])).

cnf(c_30864,plain,
    ( k2_struct_0(sK4) != X0
    | k1_zfmisc_1(k2_struct_0(sK4)) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(c_33834,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_17631,c_878])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2130,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK4)),X0)
    | r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2999,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2130])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2613,plain,
    ( ~ r2_hidden(sK0(X0,u1_struct_0(sK4)),u1_struct_0(sK4))
    | r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3000,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2613])).

cnf(c_2024,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4248,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2024])).

cnf(c_35583,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33834,c_2999,c_3000,c_4248])).

cnf(c_3930,plain,
    ( X0 != X1
    | X2 != k1_zfmisc_1(X1)
    | X2 = k1_zfmisc_1(X0) ),
    inference(resolution,[status(thm)],[c_1320,c_1323])).

cnf(c_11554,plain,
    ( X0 != X1
    | X2 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X2) ),
    inference(resolution,[status(thm)],[c_3930,c_1323])).

cnf(c_47492,plain,
    ( X0 != k2_struct_0(sK4)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_11554,c_878])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2192,plain,
    ( ~ m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X0))
    | r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_60594,plain,
    ( ~ m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(k2_struct_0(sK4)))
    | r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2192])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2059,plain,
    ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X0)
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
    | ~ r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_61297,plain,
    ( ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4))
    | ~ r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2059])).

cnf(c_1322,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_825,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_826,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_825])).

cnf(c_830,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_826,c_30,c_29,c_28,c_26])).

cnf(c_5009,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | ~ r2_hidden(X2,k1_orders_2(sK4,X0))
    | X1 != X2 ),
    inference(resolution,[status(thm)],[c_1322,c_830])).

cnf(c_2924,plain,
    ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_11,c_25])).

cnf(c_5245,plain,
    ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,a_2_0_orders_2(sK4,k2_struct_0(sK4)))
    | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_5009,c_2924])).

cnf(c_5448,plain,
    ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_5245,c_1319])).

cnf(c_95161,plain,
    ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5448,c_26,c_55,c_73,c_1336,c_1337,c_1344,c_2948,c_2999,c_3000,c_4248,c_5098,c_7038])).

cnf(c_4999,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1322,c_1319])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_738,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3(X2,X1,X0) = X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | sK3(X1,sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_738])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | sK3(X1,sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_739,c_30,c_29,c_28,c_26])).

cnf(c_9330,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | r2_hidden(sK3(X1,sK4,X0),X2) ),
    inference(resolution,[status(thm)],[c_4999,c_743])).

cnf(c_14,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_882,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_883,plain,
    ( ~ r2_orders_2(sK4,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_882])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f69])).

cnf(c_664,plain,
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
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_665,plain,
    ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_669,plain,
    ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_665,c_30,c_29,c_28,c_26])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_685,plain,
    ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_669,c_7])).

cnf(c_2645,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
    inference(resolution,[status(thm)],[c_883,c_685])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_717,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_27])).

cnf(c_718,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_717])).

cnf(c_722,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_718,c_30,c_29,c_28,c_26])).

cnf(c_924,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,a_2_0_orders_2(sK4,X1))
    | X0 != X2
    | sK3(X3,sK4,X1) != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_685,c_883])).

cnf(c_925,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_924])).

cnf(c_2696,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2645,c_722,c_925])).

cnf(c_12059,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0)) ),
    inference(resolution,[status(thm)],[c_9330,c_2696])).

cnf(c_95181,plain,
    ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_95161,c_12059])).

cnf(c_101241,plain,
    ( X0 != k2_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33886,c_26,c_25,c_55,c_73,c_1336,c_1337,c_1344,c_1979,c_2302,c_2948,c_2999,c_3000,c_3069,c_3461,c_3793,c_4248,c_4560,c_5098,c_7038,c_11898,c_12532,c_30864,c_47492,c_60594,c_61297,c_95181])).

cnf(c_101249,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_101241,c_878])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:14:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 39.42/5.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.42/5.49  
% 39.42/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.42/5.49  
% 39.42/5.49  ------  iProver source info
% 39.42/5.49  
% 39.42/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.42/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.42/5.49  git: non_committed_changes: false
% 39.42/5.49  git: last_make_outside_of_git: false
% 39.42/5.49  
% 39.42/5.49  ------ 
% 39.42/5.49  ------ Parsing...
% 39.42/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.42/5.49  
% 39.42/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 39.42/5.49  
% 39.42/5.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.42/5.49  
% 39.42/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.42/5.49  ------ Proving...
% 39.42/5.49  ------ Problem Properties 
% 39.42/5.49  
% 39.42/5.49  
% 39.42/5.49  clauses                                 23
% 39.42/5.49  conjectures                             1
% 39.42/5.49  EPR                                     3
% 39.42/5.49  Horn                                    19
% 39.42/5.49  unary                                   4
% 39.42/5.49  binary                                  9
% 39.42/5.49  lits                                    56
% 39.42/5.49  lits eq                                 9
% 39.42/5.49  fd_pure                                 0
% 39.42/5.49  fd_pseudo                               0
% 39.42/5.49  fd_cond                                 3
% 39.42/5.49  fd_pseudo_cond                          0
% 39.42/5.49  AC symbols                              0
% 39.42/5.49  
% 39.42/5.49  ------ Input Options Time Limit: Unbounded
% 39.42/5.49  
% 39.42/5.49  
% 39.42/5.49  ------ 
% 39.42/5.49  Current options:
% 39.42/5.49  ------ 
% 39.42/5.49  
% 39.42/5.49  
% 39.42/5.49  
% 39.42/5.49  
% 39.42/5.49  ------ Proving...
% 39.42/5.49  
% 39.42/5.49  
% 39.42/5.49  % SZS status Theorem for theBenchmark.p
% 39.42/5.49  
% 39.42/5.49   Resolution empty clause
% 39.42/5.49  
% 39.42/5.49  % SZS output start CNFRefutation for theBenchmark.p
% 39.42/5.49  
% 39.42/5.49  fof(f12,axiom,(
% 39.42/5.49    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 39.42/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.49  
% 39.42/5.49  fof(f27,plain,(
% 39.42/5.49    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 39.42/5.49    inference(ennf_transformation,[],[f12])).
% 39.42/5.49  
% 39.42/5.49  fof(f66,plain,(
% 39.42/5.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 39.42/5.49    inference(cnf_transformation,[],[f27])).
% 39.42/5.49  
% 39.42/5.49  fof(f8,axiom,(
% 39.42/5.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 39.42/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.49  
% 39.42/5.49  fof(f21,plain,(
% 39.42/5.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 39.42/5.49    inference(ennf_transformation,[],[f8])).
% 39.42/5.49  
% 39.42/5.49  fof(f60,plain,(
% 39.42/5.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 39.42/5.49    inference(cnf_transformation,[],[f21])).
% 39.42/5.49  
% 39.42/5.49  fof(f14,conjecture,(
% 39.42/5.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 39.42/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.49  
% 39.42/5.49  fof(f15,negated_conjecture,(
% 39.42/5.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 39.42/5.49    inference(negated_conjecture,[],[f14])).
% 39.42/5.49  
% 39.42/5.49  fof(f30,plain,(
% 39.42/5.49    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 39.42/5.49    inference(ennf_transformation,[],[f15])).
% 39.42/5.49  
% 39.42/5.49  fof(f31,plain,(
% 39.42/5.49    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 39.42/5.49    inference(flattening,[],[f30])).
% 39.42/5.49  
% 39.42/5.49  fof(f46,plain,(
% 39.42/5.49    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4))),
% 39.42/5.49    introduced(choice_axiom,[])).
% 39.42/5.49  
% 39.42/5.49  fof(f47,plain,(
% 39.42/5.49    k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4)),
% 39.42/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f46])).
% 39.42/5.49  
% 39.42/5.49  fof(f77,plain,(
% 39.42/5.49    l1_orders_2(sK4)),
% 39.42/5.49    inference(cnf_transformation,[],[f47])).
% 39.42/5.49  
% 39.42/5.49  fof(f4,axiom,(
% 39.42/5.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 39.42/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.49  
% 39.42/5.49  fof(f36,plain,(
% 39.42/5.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 39.42/5.49    inference(nnf_transformation,[],[f4])).
% 39.42/5.49  
% 39.42/5.49  fof(f54,plain,(
% 39.42/5.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 39.42/5.49    inference(cnf_transformation,[],[f36])).
% 39.42/5.49  
% 39.42/5.49  fof(f78,plain,(
% 39.42/5.49    k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4))),
% 39.42/5.49    inference(cnf_transformation,[],[f47])).
% 39.42/5.49  
% 39.42/5.49  fof(f7,axiom,(
% 39.42/5.49    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 39.42/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.49  
% 39.42/5.49  fof(f20,plain,(
% 39.42/5.49    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 39.42/5.49    inference(ennf_transformation,[],[f7])).
% 39.42/5.49  
% 39.42/5.49  fof(f37,plain,(
% 39.42/5.49    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 39.42/5.49    introduced(choice_axiom,[])).
% 39.42/5.49  
% 39.42/5.49  fof(f38,plain,(
% 39.42/5.49    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 39.42/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f37])).
% 39.42/5.49  
% 39.42/5.49  fof(f57,plain,(
% 39.42/5.49    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 39.42/5.49    inference(cnf_transformation,[],[f38])).
% 39.42/5.49  
% 39.42/5.49  fof(f11,axiom,(
% 39.42/5.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 39.42/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.49  
% 39.42/5.49  fof(f25,plain,(
% 39.42/5.49    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 39.42/5.49    inference(ennf_transformation,[],[f11])).
% 39.42/5.49  
% 39.42/5.49  fof(f26,plain,(
% 39.42/5.49    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 39.42/5.49    inference(flattening,[],[f25])).
% 39.42/5.49  
% 39.42/5.49  fof(f65,plain,(
% 39.42/5.49    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 39.42/5.49    inference(cnf_transformation,[],[f26])).
% 39.42/5.49  
% 39.42/5.49  fof(f76,plain,(
% 39.42/5.49    v5_orders_2(sK4)),
% 39.42/5.49    inference(cnf_transformation,[],[f47])).
% 39.42/5.49  
% 39.42/5.49  fof(f73,plain,(
% 39.42/5.49    ~v2_struct_0(sK4)),
% 39.42/5.49    inference(cnf_transformation,[],[f47])).
% 39.42/5.49  
% 39.42/5.49  fof(f74,plain,(
% 39.42/5.49    v3_orders_2(sK4)),
% 39.42/5.49    inference(cnf_transformation,[],[f47])).
% 39.42/5.49  
% 39.42/5.49  fof(f75,plain,(
% 39.42/5.49    v4_orders_2(sK4)),
% 39.42/5.49    inference(cnf_transformation,[],[f47])).
% 39.42/5.49  
% 39.42/5.49  fof(f1,axiom,(
% 39.42/5.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 39.42/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.49  
% 39.42/5.49  fof(f16,plain,(
% 39.42/5.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 39.42/5.49    inference(ennf_transformation,[],[f1])).
% 39.42/5.49  
% 39.42/5.49  fof(f32,plain,(
% 39.42/5.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 39.42/5.49    inference(nnf_transformation,[],[f16])).
% 39.42/5.49  
% 39.42/5.49  fof(f33,plain,(
% 39.42/5.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 39.42/5.49    inference(rectify,[],[f32])).
% 39.42/5.49  
% 39.42/5.49  fof(f34,plain,(
% 39.42/5.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 39.42/5.49    introduced(choice_axiom,[])).
% 39.42/5.49  
% 39.42/5.49  fof(f35,plain,(
% 39.42/5.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 39.42/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 39.42/5.49  
% 39.42/5.49  fof(f49,plain,(
% 39.42/5.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 39.42/5.49    inference(cnf_transformation,[],[f35])).
% 39.42/5.49  
% 39.42/5.49  fof(f50,plain,(
% 39.42/5.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 39.42/5.49    inference(cnf_transformation,[],[f35])).
% 39.42/5.49  
% 39.42/5.49  fof(f53,plain,(
% 39.42/5.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 39.42/5.49    inference(cnf_transformation,[],[f36])).
% 39.42/5.49  
% 39.42/5.49  fof(f48,plain,(
% 39.42/5.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 39.42/5.49    inference(cnf_transformation,[],[f35])).
% 39.42/5.49  
% 39.42/5.49  fof(f10,axiom,(
% 39.42/5.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 39.42/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.49  
% 39.42/5.49  fof(f23,plain,(
% 39.42/5.49    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 39.42/5.49    inference(ennf_transformation,[],[f10])).
% 39.42/5.49  
% 39.42/5.49  fof(f24,plain,(
% 39.42/5.49    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 39.42/5.49    inference(flattening,[],[f23])).
% 39.42/5.49  
% 39.42/5.49  fof(f64,plain,(
% 39.42/5.49    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 39.42/5.49    inference(cnf_transformation,[],[f24])).
% 39.42/5.49  
% 39.42/5.49  fof(f13,axiom,(
% 39.42/5.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 39.42/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.49  
% 39.42/5.49  fof(f28,plain,(
% 39.42/5.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 39.42/5.49    inference(ennf_transformation,[],[f13])).
% 39.42/5.49  
% 39.42/5.49  fof(f29,plain,(
% 39.42/5.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 39.42/5.49    inference(flattening,[],[f28])).
% 39.42/5.49  
% 39.42/5.49  fof(f41,plain,(
% 39.42/5.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 39.42/5.49    inference(nnf_transformation,[],[f29])).
% 39.42/5.49  
% 39.42/5.49  fof(f42,plain,(
% 39.42/5.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 39.42/5.49    inference(rectify,[],[f41])).
% 39.42/5.49  
% 39.42/5.49  fof(f44,plain,(
% 39.42/5.49    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK3(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 39.42/5.49    introduced(choice_axiom,[])).
% 39.42/5.49  
% 39.42/5.49  fof(f43,plain,(
% 39.42/5.49    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK2(X1,X2,X3),X3) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))))),
% 39.42/5.49    introduced(choice_axiom,[])).
% 39.42/5.49  
% 39.42/5.49  fof(f45,plain,(
% 39.42/5.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK2(X1,X2,X3),X3) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK3(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 39.42/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f44,f43])).
% 39.42/5.49  
% 39.42/5.49  fof(f68,plain,(
% 39.42/5.49    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 39.42/5.49    inference(cnf_transformation,[],[f45])).
% 39.42/5.49  
% 39.42/5.49  fof(f9,axiom,(
% 39.42/5.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 39.42/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.49  
% 39.42/5.49  fof(f22,plain,(
% 39.42/5.49    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 39.42/5.49    inference(ennf_transformation,[],[f9])).
% 39.42/5.49  
% 39.42/5.49  fof(f39,plain,(
% 39.42/5.49    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 39.42/5.49    inference(nnf_transformation,[],[f22])).
% 39.42/5.49  
% 39.42/5.49  fof(f40,plain,(
% 39.42/5.49    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 39.42/5.49    inference(flattening,[],[f39])).
% 39.42/5.49  
% 39.42/5.49  fof(f62,plain,(
% 39.42/5.49    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 39.42/5.49    inference(cnf_transformation,[],[f40])).
% 39.42/5.49  
% 39.42/5.49  fof(f79,plain,(
% 39.42/5.49    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 39.42/5.49    inference(equality_resolution,[],[f62])).
% 39.42/5.49  
% 39.42/5.49  fof(f69,plain,(
% 39.42/5.49    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK3(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 39.42/5.49    inference(cnf_transformation,[],[f45])).
% 39.42/5.49  
% 39.42/5.49  fof(f5,axiom,(
% 39.42/5.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 39.42/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.49  
% 39.42/5.49  fof(f17,plain,(
% 39.42/5.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 39.42/5.49    inference(ennf_transformation,[],[f5])).
% 39.42/5.49  
% 39.42/5.49  fof(f18,plain,(
% 39.42/5.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 39.42/5.49    inference(flattening,[],[f17])).
% 39.42/5.49  
% 39.42/5.49  fof(f55,plain,(
% 39.42/5.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 39.42/5.49    inference(cnf_transformation,[],[f18])).
% 39.42/5.49  
% 39.42/5.49  fof(f67,plain,(
% 39.42/5.49    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 39.42/5.49    inference(cnf_transformation,[],[f45])).
% 39.42/5.49  
% 39.42/5.49  cnf(c_1324,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.42/5.49      theory(equality) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_1323,plain,
% 39.42/5.49      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 39.42/5.49      theory(equality) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_6140,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.42/5.49      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 39.42/5.49      | X2 != X0
% 39.42/5.49      | X3 != X1 ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_1324,c_1323]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_18,plain,
% 39.42/5.49      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 39.42/5.49      inference(cnf_transformation,[],[f66]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_12,plain,
% 39.42/5.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 39.42/5.49      inference(cnf_transformation,[],[f60]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_411,plain,
% 39.42/5.49      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_18,c_12]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_26,negated_conjecture,
% 39.42/5.49      ( l1_orders_2(sK4) ),
% 39.42/5.49      inference(cnf_transformation,[],[f77]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_877,plain,
% 39.42/5.49      ( u1_struct_0(X0) = k2_struct_0(X0) | sK4 != X0 ),
% 39.42/5.49      inference(resolution_lifted,[status(thm)],[c_411,c_26]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_878,plain,
% 39.42/5.49      ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 39.42/5.49      inference(unflattening,[status(thm)],[c_877]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_17030,plain,
% 39.42/5.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK4)))
% 39.42/5.49      | X0 != X1 ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_6140,c_878]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_5,plain,
% 39.42/5.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.42/5.49      inference(cnf_transformation,[],[f54]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_17631,plain,
% 39.42/5.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ r1_tarski(X1,k2_struct_0(sK4))
% 39.42/5.49      | X0 != X1 ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_17030,c_5]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_1320,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_3927,plain,
% 39.42/5.49      ( X0 = u1_struct_0(sK4) | X0 != k2_struct_0(sK4) ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_1320,c_878]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_33886,plain,
% 39.42/5.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ r1_tarski(u1_struct_0(sK4),k2_struct_0(sK4))
% 39.42/5.49      | X0 != k2_struct_0(sK4) ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_17631,c_3927]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_25,negated_conjecture,
% 39.42/5.49      ( k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) ),
% 39.42/5.49      inference(cnf_transformation,[],[f78]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_55,plain,
% 39.42/5.49      ( ~ l1_orders_2(sK4) | l1_struct_0(sK4) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_18]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_73,plain,
% 39.42/5.49      ( ~ l1_struct_0(sK4) | u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_12]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_1325,plain,
% 39.42/5.49      ( X0 != X1 | k2_struct_0(X0) = k2_struct_0(X1) ),
% 39.42/5.49      theory(equality) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_1336,plain,
% 39.42/5.49      ( k2_struct_0(sK4) = k2_struct_0(sK4) | sK4 != sK4 ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_1325]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_1326,plain,
% 39.42/5.49      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 39.42/5.49      theory(equality) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_1337,plain,
% 39.42/5.49      ( u1_struct_0(sK4) = u1_struct_0(sK4) | sK4 != sK4 ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_1326]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_1319,plain,( X0 = X0 ),theory(equality) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_1344,plain,
% 39.42/5.49      ( sK4 = sK4 ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_1319]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_11,plain,
% 39.42/5.49      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 39.42/5.49      inference(cnf_transformation,[],[f57]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_1979,plain,
% 39.42/5.49      ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
% 39.42/5.49      | k1_xboole_0 = k1_orders_2(sK4,k2_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_11]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2302,plain,
% 39.42/5.49      ( k1_orders_2(sK4,k2_struct_0(sK4)) = k1_orders_2(sK4,k2_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_1319]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2948,plain,
% 39.42/5.49      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 39.42/5.49      | k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_1323]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2311,plain,
% 39.42/5.49      ( X0 != X1 | k2_struct_0(sK4) != X1 | k2_struct_0(sK4) = X0 ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_1320]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_3069,plain,
% 39.42/5.49      ( X0 != k2_struct_0(sK4)
% 39.42/5.49      | k2_struct_0(sK4) = X0
% 39.42/5.49      | k2_struct_0(sK4) != k2_struct_0(sK4) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2311]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_1328,plain,
% 39.42/5.49      ( X0 != X1 | X2 != X3 | k1_orders_2(X0,X2) = k1_orders_2(X1,X3) ),
% 39.42/5.49      theory(equality) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2796,plain,
% 39.42/5.49      ( X0 != k2_struct_0(sK4)
% 39.42/5.49      | X1 != sK4
% 39.42/5.49      | k1_orders_2(X1,X0) = k1_orders_2(sK4,k2_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_1328]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_3460,plain,
% 39.42/5.49      ( X0 != sK4
% 39.42/5.49      | k1_orders_2(X0,u1_struct_0(sK4)) = k1_orders_2(sK4,k2_struct_0(sK4))
% 39.42/5.49      | u1_struct_0(sK4) != k2_struct_0(sK4) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2796]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_3461,plain,
% 39.42/5.49      ( k1_orders_2(sK4,u1_struct_0(sK4)) = k1_orders_2(sK4,k2_struct_0(sK4))
% 39.42/5.49      | u1_struct_0(sK4) != k2_struct_0(sK4)
% 39.42/5.49      | sK4 != sK4 ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_3460]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2093,plain,
% 39.42/5.49      ( X0 != X1
% 39.42/5.49      | k1_orders_2(sK4,k2_struct_0(sK4)) != X1
% 39.42/5.49      | k1_orders_2(sK4,k2_struct_0(sK4)) = X0 ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_1320]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2301,plain,
% 39.42/5.49      ( X0 != k1_orders_2(sK4,k2_struct_0(sK4))
% 39.42/5.49      | k1_orders_2(sK4,k2_struct_0(sK4)) = X0
% 39.42/5.49      | k1_orders_2(sK4,k2_struct_0(sK4)) != k1_orders_2(sK4,k2_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2093]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_3791,plain,
% 39.42/5.49      ( k1_orders_2(X0,u1_struct_0(sK4)) != k1_orders_2(sK4,k2_struct_0(sK4))
% 39.42/5.49      | k1_orders_2(sK4,k2_struct_0(sK4)) = k1_orders_2(X0,u1_struct_0(sK4))
% 39.42/5.49      | k1_orders_2(sK4,k2_struct_0(sK4)) != k1_orders_2(sK4,k2_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2301]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_3793,plain,
% 39.42/5.49      ( k1_orders_2(sK4,u1_struct_0(sK4)) != k1_orders_2(sK4,k2_struct_0(sK4))
% 39.42/5.49      | k1_orders_2(sK4,k2_struct_0(sK4)) = k1_orders_2(sK4,u1_struct_0(sK4))
% 39.42/5.49      | k1_orders_2(sK4,k2_struct_0(sK4)) != k1_orders_2(sK4,k2_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_3791]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_17,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.42/5.49      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 39.42/5.49      | v2_struct_0(X1)
% 39.42/5.49      | ~ v3_orders_2(X1)
% 39.42/5.49      | ~ v4_orders_2(X1)
% 39.42/5.49      | ~ v5_orders_2(X1)
% 39.42/5.49      | ~ l1_orders_2(X1) ),
% 39.42/5.49      inference(cnf_transformation,[],[f65]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_27,negated_conjecture,
% 39.42/5.49      ( v5_orders_2(sK4) ),
% 39.42/5.49      inference(cnf_transformation,[],[f76]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_807,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.42/5.49      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 39.42/5.49      | v2_struct_0(X1)
% 39.42/5.49      | ~ v3_orders_2(X1)
% 39.42/5.49      | ~ v4_orders_2(X1)
% 39.42/5.49      | ~ l1_orders_2(X1)
% 39.42/5.49      | sK4 != X1 ),
% 39.42/5.49      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_808,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | v2_struct_0(sK4)
% 39.42/5.49      | ~ v3_orders_2(sK4)
% 39.42/5.49      | ~ v4_orders_2(sK4)
% 39.42/5.49      | ~ l1_orders_2(sK4) ),
% 39.42/5.49      inference(unflattening,[status(thm)],[c_807]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_30,negated_conjecture,
% 39.42/5.49      ( ~ v2_struct_0(sK4) ),
% 39.42/5.49      inference(cnf_transformation,[],[f73]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_29,negated_conjecture,
% 39.42/5.49      ( v3_orders_2(sK4) ),
% 39.42/5.49      inference(cnf_transformation,[],[f74]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_28,negated_conjecture,
% 39.42/5.49      ( v4_orders_2(sK4) ),
% 39.42/5.49      inference(cnf_transformation,[],[f75]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_812,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 39.42/5.49      inference(global_propositional_subsumption,
% 39.42/5.49                [status(thm)],
% 39.42/5.49                [c_808,c_30,c_29,c_28,c_26]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_4560,plain,
% 39.42/5.49      ( m1_subset_1(k1_orders_2(sK4,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_812]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_5098,plain,
% 39.42/5.49      ( u1_struct_0(sK4) != k2_struct_0(sK4)
% 39.42/5.49      | k2_struct_0(sK4) = u1_struct_0(sK4)
% 39.42/5.49      | k2_struct_0(sK4) != k2_struct_0(sK4) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_3069]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2019,plain,
% 39.42/5.49      ( m1_subset_1(X0,X1)
% 39.42/5.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 39.42/5.49      | X0 != X2
% 39.42/5.49      | X1 != k1_zfmisc_1(X3) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_1324]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2164,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.42/5.49      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 39.42/5.49      | X2 != X0
% 39.42/5.49      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2019]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2603,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | k2_struct_0(sK4) != X0
% 39.42/5.49      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2164]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_7038,plain,
% 39.42/5.49      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | k2_struct_0(sK4) != u1_struct_0(sK4)
% 39.42/5.49      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2603]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2171,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.42/5.49      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 39.42/5.49      | X2 != X0
% 39.42/5.49      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2019]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2593,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.42/5.49      | m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X2))
% 39.42/5.49      | k1_orders_2(sK4,k2_struct_0(sK4)) != X0
% 39.42/5.49      | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2171]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_3199,plain,
% 39.42/5.49      ( ~ m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X0))
% 39.42/5.49      | m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X1))
% 39.42/5.49      | k1_orders_2(sK4,k2_struct_0(sK4)) != k1_orders_2(sK4,k2_struct_0(sK4))
% 39.42/5.49      | k1_zfmisc_1(X1) != k1_zfmisc_1(X0) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2593]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_11898,plain,
% 39.42/5.49      ( ~ m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X0))
% 39.42/5.49      | m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(k2_struct_0(sK4)))
% 39.42/5.49      | k1_orders_2(sK4,k2_struct_0(sK4)) != k1_orders_2(sK4,k2_struct_0(sK4))
% 39.42/5.49      | k1_zfmisc_1(k2_struct_0(sK4)) != k1_zfmisc_1(X0) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_3199]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_4573,plain,
% 39.42/5.49      ( ~ m1_subset_1(k1_orders_2(X0,u1_struct_0(sK4)),k1_zfmisc_1(X1))
% 39.42/5.49      | m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X2))
% 39.42/5.49      | k1_orders_2(sK4,k2_struct_0(sK4)) != k1_orders_2(X0,u1_struct_0(sK4))
% 39.42/5.49      | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2593]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_12532,plain,
% 39.42/5.49      ( ~ m1_subset_1(k1_orders_2(sK4,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X0))
% 39.42/5.49      | k1_orders_2(sK4,k2_struct_0(sK4)) != k1_orders_2(sK4,u1_struct_0(sK4))
% 39.42/5.49      | k1_zfmisc_1(X0) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_4573]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_30864,plain,
% 39.42/5.49      ( k2_struct_0(sK4) != X0
% 39.42/5.49      | k1_zfmisc_1(k2_struct_0(sK4)) = k1_zfmisc_1(X0) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_1323]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_33834,plain,
% 39.42/5.49      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4)) ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_17631,c_878]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_1,plain,
% 39.42/5.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 39.42/5.49      inference(cnf_transformation,[],[f49]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2130,plain,
% 39.42/5.49      ( r2_hidden(sK0(X0,u1_struct_0(sK4)),X0)
% 39.42/5.49      | r1_tarski(X0,u1_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_1]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2999,plain,
% 39.42/5.49      ( r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
% 39.42/5.49      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2130]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_0,plain,
% 39.42/5.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 39.42/5.49      inference(cnf_transformation,[],[f50]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2613,plain,
% 39.42/5.49      ( ~ r2_hidden(sK0(X0,u1_struct_0(sK4)),u1_struct_0(sK4))
% 39.42/5.49      | r1_tarski(X0,u1_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_0]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_3000,plain,
% 39.42/5.49      ( ~ r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
% 39.42/5.49      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2613]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2024,plain,
% 39.42/5.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_5]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_4248,plain,
% 39.42/5.49      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2024]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_35583,plain,
% 39.42/5.49      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 39.42/5.49      inference(global_propositional_subsumption,
% 39.42/5.49                [status(thm)],
% 39.42/5.49                [c_33834,c_2999,c_3000,c_4248]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_3930,plain,
% 39.42/5.49      ( X0 != X1 | X2 != k1_zfmisc_1(X1) | X2 = k1_zfmisc_1(X0) ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_1320,c_1323]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_11554,plain,
% 39.42/5.49      ( X0 != X1 | X2 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X2) ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_3930,c_1323]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_47492,plain,
% 39.42/5.49      ( X0 != k2_struct_0(sK4)
% 39.42/5.49      | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK4)) ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_11554,c_878]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_6,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 39.42/5.49      inference(cnf_transformation,[],[f53]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2192,plain,
% 39.42/5.49      ( ~ m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X0))
% 39.42/5.49      | r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),X0) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_6]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_60594,plain,
% 39.42/5.49      ( ~ m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(k2_struct_0(sK4)))
% 39.42/5.49      | r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),k2_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2192]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2,plain,
% 39.42/5.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 39.42/5.49      inference(cnf_transformation,[],[f48]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2059,plain,
% 39.42/5.49      ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X0)
% 39.42/5.49      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
% 39.42/5.49      | ~ r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),X0) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_61297,plain,
% 39.42/5.49      ( ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
% 39.42/5.49      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4))
% 39.42/5.49      | ~ r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),k2_struct_0(sK4)) ),
% 39.42/5.49      inference(instantiation,[status(thm)],[c_2059]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_1322,plain,
% 39.42/5.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.42/5.49      theory(equality) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_16,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.42/5.49      | v2_struct_0(X1)
% 39.42/5.49      | ~ v3_orders_2(X1)
% 39.42/5.49      | ~ v4_orders_2(X1)
% 39.42/5.49      | ~ v5_orders_2(X1)
% 39.42/5.49      | ~ l1_orders_2(X1)
% 39.42/5.49      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 39.42/5.49      inference(cnf_transformation,[],[f64]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_825,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.42/5.49      | v2_struct_0(X1)
% 39.42/5.49      | ~ v3_orders_2(X1)
% 39.42/5.49      | ~ v4_orders_2(X1)
% 39.42/5.49      | ~ l1_orders_2(X1)
% 39.42/5.49      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
% 39.42/5.49      | sK4 != X1 ),
% 39.42/5.49      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_826,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | v2_struct_0(sK4)
% 39.42/5.49      | ~ v3_orders_2(sK4)
% 39.42/5.49      | ~ v4_orders_2(sK4)
% 39.42/5.49      | ~ l1_orders_2(sK4)
% 39.42/5.49      | a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0) ),
% 39.42/5.49      inference(unflattening,[status(thm)],[c_825]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_830,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0) ),
% 39.42/5.49      inference(global_propositional_subsumption,
% 39.42/5.49                [status(thm)],
% 39.42/5.49                [c_826,c_30,c_29,c_28,c_26]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_5009,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.42/5.49      | ~ r2_hidden(X2,k1_orders_2(sK4,X0))
% 39.42/5.49      | X1 != X2 ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_1322,c_830]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2924,plain,
% 39.42/5.49      ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_11,c_25]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_5245,plain,
% 39.42/5.49      ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | r2_hidden(X0,a_2_0_orders_2(sK4,k2_struct_0(sK4)))
% 39.42/5.49      | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_5009,c_2924]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_5448,plain,
% 39.42/5.49      ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,k2_struct_0(sK4))) ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_5245,c_1319]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_95161,plain,
% 39.42/5.49      ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,k2_struct_0(sK4))) ),
% 39.42/5.49      inference(global_propositional_subsumption,
% 39.42/5.49                [status(thm)],
% 39.42/5.49                [c_5448,c_26,c_55,c_73,c_1336,c_1337,c_1344,c_2948,c_2999,
% 39.42/5.49                 c_3000,c_4248,c_5098,c_7038]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_4999,plain,
% 39.42/5.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_1322,c_1319]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_23,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.42/5.49      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 39.42/5.49      | v2_struct_0(X1)
% 39.42/5.49      | ~ v3_orders_2(X1)
% 39.42/5.49      | ~ v4_orders_2(X1)
% 39.42/5.49      | ~ v5_orders_2(X1)
% 39.42/5.49      | ~ l1_orders_2(X1)
% 39.42/5.49      | sK3(X2,X1,X0) = X2 ),
% 39.42/5.49      inference(cnf_transformation,[],[f68]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_738,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.42/5.49      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 39.42/5.49      | v2_struct_0(X1)
% 39.42/5.49      | ~ v3_orders_2(X1)
% 39.42/5.49      | ~ v4_orders_2(X1)
% 39.42/5.49      | ~ l1_orders_2(X1)
% 39.42/5.49      | sK3(X2,X1,X0) = X2
% 39.42/5.49      | sK4 != X1 ),
% 39.42/5.49      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_739,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.42/5.49      | v2_struct_0(sK4)
% 39.42/5.49      | ~ v3_orders_2(sK4)
% 39.42/5.49      | ~ v4_orders_2(sK4)
% 39.42/5.49      | ~ l1_orders_2(sK4)
% 39.42/5.49      | sK3(X1,sK4,X0) = X1 ),
% 39.42/5.49      inference(unflattening,[status(thm)],[c_738]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_743,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.42/5.49      | sK3(X1,sK4,X0) = X1 ),
% 39.42/5.49      inference(global_propositional_subsumption,
% 39.42/5.49                [status(thm)],
% 39.42/5.49                [c_739,c_30,c_29,c_28,c_26]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_9330,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ r2_hidden(X1,X2)
% 39.42/5.49      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.42/5.49      | r2_hidden(sK3(X1,sK4,X0),X2) ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_4999,c_743]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_14,plain,
% 39.42/5.49      ( ~ r2_orders_2(X0,X1,X1)
% 39.42/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.42/5.49      | ~ l1_orders_2(X0) ),
% 39.42/5.49      inference(cnf_transformation,[],[f79]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_882,plain,
% 39.42/5.49      ( ~ r2_orders_2(X0,X1,X1)
% 39.42/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.42/5.49      | sK4 != X0 ),
% 39.42/5.49      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_883,plain,
% 39.42/5.49      ( ~ r2_orders_2(sK4,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 39.42/5.49      inference(unflattening,[status(thm)],[c_882]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_22,plain,
% 39.42/5.49      ( r2_orders_2(X0,X1,sK3(X2,X0,X3))
% 39.42/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.42/5.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 39.42/5.49      | ~ r2_hidden(X1,X3)
% 39.42/5.49      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 39.42/5.49      | v2_struct_0(X0)
% 39.42/5.49      | ~ v3_orders_2(X0)
% 39.42/5.49      | ~ v4_orders_2(X0)
% 39.42/5.49      | ~ v5_orders_2(X0)
% 39.42/5.49      | ~ l1_orders_2(X0) ),
% 39.42/5.49      inference(cnf_transformation,[],[f69]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_664,plain,
% 39.42/5.49      ( r2_orders_2(X0,X1,sK3(X2,X0,X3))
% 39.42/5.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.42/5.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 39.42/5.49      | ~ r2_hidden(X1,X3)
% 39.42/5.49      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 39.42/5.49      | v2_struct_0(X0)
% 39.42/5.49      | ~ v3_orders_2(X0)
% 39.42/5.49      | ~ v4_orders_2(X0)
% 39.42/5.49      | ~ l1_orders_2(X0)
% 39.42/5.49      | sK4 != X0 ),
% 39.42/5.49      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_665,plain,
% 39.42/5.49      ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
% 39.42/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 39.42/5.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ r2_hidden(X0,X2)
% 39.42/5.49      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2))
% 39.42/5.49      | v2_struct_0(sK4)
% 39.42/5.49      | ~ v3_orders_2(sK4)
% 39.42/5.49      | ~ v4_orders_2(sK4)
% 39.42/5.49      | ~ l1_orders_2(sK4) ),
% 39.42/5.49      inference(unflattening,[status(thm)],[c_664]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_669,plain,
% 39.42/5.49      ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
% 39.42/5.49      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 39.42/5.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ r2_hidden(X0,X2)
% 39.42/5.49      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2)) ),
% 39.42/5.49      inference(global_propositional_subsumption,
% 39.42/5.49                [status(thm)],
% 39.42/5.49                [c_665,c_30,c_29,c_28,c_26]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_7,plain,
% 39.42/5.49      ( m1_subset_1(X0,X1)
% 39.42/5.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 39.42/5.49      | ~ r2_hidden(X0,X2) ),
% 39.42/5.49      inference(cnf_transformation,[],[f55]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_685,plain,
% 39.42/5.49      ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
% 39.42/5.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ r2_hidden(X0,X2)
% 39.42/5.49      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2)) ),
% 39.42/5.49      inference(forward_subsumption_resolution,[status(thm)],[c_669,c_7]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2645,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
% 39.42/5.49      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.42/5.49      | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_883,c_685]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_24,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.42/5.49      | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
% 39.42/5.49      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 39.42/5.49      | v2_struct_0(X1)
% 39.42/5.49      | ~ v3_orders_2(X1)
% 39.42/5.49      | ~ v4_orders_2(X1)
% 39.42/5.49      | ~ v5_orders_2(X1)
% 39.42/5.49      | ~ l1_orders_2(X1) ),
% 39.42/5.49      inference(cnf_transformation,[],[f67]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_717,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.42/5.49      | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
% 39.42/5.49      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 39.42/5.49      | v2_struct_0(X1)
% 39.42/5.49      | ~ v3_orders_2(X1)
% 39.42/5.49      | ~ v4_orders_2(X1)
% 39.42/5.49      | ~ l1_orders_2(X1)
% 39.42/5.49      | sK4 != X1 ),
% 39.42/5.49      inference(resolution_lifted,[status(thm)],[c_24,c_27]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_718,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
% 39.42/5.49      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.42/5.49      | v2_struct_0(sK4)
% 39.42/5.49      | ~ v3_orders_2(sK4)
% 39.42/5.49      | ~ v4_orders_2(sK4)
% 39.42/5.49      | ~ l1_orders_2(sK4) ),
% 39.42/5.49      inference(unflattening,[status(thm)],[c_717]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_722,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
% 39.42/5.49      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0)) ),
% 39.42/5.49      inference(global_propositional_subsumption,
% 39.42/5.49                [status(thm)],
% 39.42/5.49                [c_718,c_30,c_29,c_28,c_26]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_924,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 39.42/5.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ r2_hidden(X2,X1)
% 39.42/5.49      | ~ r2_hidden(X3,a_2_0_orders_2(sK4,X1))
% 39.42/5.49      | X0 != X2
% 39.42/5.49      | sK3(X3,sK4,X1) != X0
% 39.42/5.49      | sK4 != sK4 ),
% 39.42/5.49      inference(resolution_lifted,[status(thm)],[c_685,c_883]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_925,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
% 39.42/5.49      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.42/5.49      | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
% 39.42/5.49      inference(unflattening,[status(thm)],[c_924]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_2696,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.42/5.49      | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
% 39.42/5.49      inference(global_propositional_subsumption,
% 39.42/5.49                [status(thm)],
% 39.42/5.49                [c_2645,c_722,c_925]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_12059,plain,
% 39.42/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ r2_hidden(X1,X0)
% 39.42/5.49      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0)) ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_9330,c_2696]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_95181,plain,
% 39.42/5.49      ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.42/5.49      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k2_struct_0(sK4)) ),
% 39.42/5.49      inference(resolution,[status(thm)],[c_95161,c_12059]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_101241,plain,
% 39.42/5.49      ( X0 != k2_struct_0(sK4) ),
% 39.42/5.49      inference(global_propositional_subsumption,
% 39.42/5.49                [status(thm)],
% 39.42/5.49                [c_33886,c_26,c_25,c_55,c_73,c_1336,c_1337,c_1344,c_1979,
% 39.42/5.49                 c_2302,c_2948,c_2999,c_3000,c_3069,c_3461,c_3793,c_4248,
% 39.42/5.49                 c_4560,c_5098,c_7038,c_11898,c_12532,c_30864,c_47492,c_60594,
% 39.42/5.49                 c_61297,c_95181]) ).
% 39.42/5.49  
% 39.42/5.49  cnf(c_101249,plain,
% 39.42/5.49      ( $false ),
% 39.42/5.49      inference(backward_subsumption_resolution,[status(thm)],[c_101241,c_878]) ).
% 39.42/5.49  
% 39.42/5.49  
% 39.42/5.49  % SZS output end CNFRefutation for theBenchmark.p
% 39.42/5.49  
% 39.42/5.49  ------                               Statistics
% 39.42/5.49  
% 39.42/5.49  ------ Selected
% 39.42/5.49  
% 39.42/5.49  total_time:                             4.589
% 39.42/5.49  
%------------------------------------------------------------------------------
