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
% DateTime   : Thu Dec  3 12:12:11 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_9935)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f32])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f30,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f41,plain,
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

fof(f42,plain,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f41])).

fof(f68,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
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

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f39,plain,(
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

fof(f38,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f39,f38])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_7,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_705,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_711,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_726,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_711,c_0])).

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_691,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_698,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1229,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_691,c_698])).

cnf(c_8,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_704,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1499,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_1229,c_704])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_700,plain,
    ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3285,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1499,c_700])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_28,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_29,plain,
    ( v4_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_31,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3871,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3285,c_27,c_28,c_29,c_30,c_31])).

cnf(c_3872,plain,
    ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3871])).

cnf(c_3879,plain,
    ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_726,c_3872])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_693,plain,
    ( sK2(X0,X1,X2) = X0
    | r2_hidden(X0,a_2_1_orders_2(X1,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4220,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3879,c_693])).

cnf(c_4221,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4220,c_1499])).

cnf(c_4226,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | sK2(X0,sK3,k2_struct_0(sK3)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4221,c_27,c_28,c_29,c_30,c_31])).

cnf(c_4227,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4226])).

cnf(c_4235,plain,
    ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
    | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4227,c_726])).

cnf(c_4239,plain,
    ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
    | k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_705,c_4235])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_692,plain,
    ( r2_hidden(X0,a_2_1_orders_2(X1,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_710,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1467,plain,
    ( r2_hidden(X0,a_2_1_orders_2(X1,X2)) != iProver_top
    | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_692,c_710])).

cnf(c_9867,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4239,c_1467])).

cnf(c_10022,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9867,c_1499,c_3879])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1007,plain,
    ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
    | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1008,plain,
    ( k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3))
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1007])).

cnf(c_18,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_694,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_709,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_923,plain,
    ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_694,c_709])).

cnf(c_1616,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1499,c_692])).

cnf(c_1617,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1616,c_1499])).

cnf(c_1622,plain,
    ( m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1617,c_27,c_28,c_29,c_30,c_31])).

cnf(c_1623,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1622])).

cnf(c_10,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_702,plain,
    ( r2_orders_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2131,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1499,c_702])).

cnf(c_2489,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | r2_orders_2(sK3,X0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2131,c_31])).

cnf(c_2490,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2489])).

cnf(c_2497,plain,
    ( r2_orders_2(sK3,sK2(X0,sK3,X1),sK2(X0,sK3,X1)) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1623,c_2490])).

cnf(c_4608,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_2497])).

cnf(c_4641,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4608,c_1499])).

cnf(c_5250,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4641,c_27,c_28,c_29,c_30,c_31])).

cnf(c_5251,plain,
    ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5250])).

cnf(c_9875,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4239,c_5251])).

cnf(c_9931,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9875,c_3879])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_699,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3481,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1499,c_699])).

cnf(c_3555,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3481,c_1499])).

cnf(c_3988,plain,
    ( m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3555,c_27,c_28,c_29,c_30,c_31])).

cnf(c_3989,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3988])).

cnf(c_3997,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3989,c_709])).

cnf(c_4568,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_3997])).

cnf(c_4973,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | m1_subset_1(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_705,c_4568])).

cnf(c_5004,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4973,c_710])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_708,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3998,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3989,c_708])).

cnf(c_6846,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_3998])).

cnf(c_7783,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_705,c_6846])).

cnf(c_10370,plain,
    ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
    | k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5004,c_7783])).

cnf(c_10371,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10370])).

cnf(c_10593,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10022,c_21,c_1008,c_7783,c_9935])).

cnf(c_10599,plain,
    ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10593,c_726])).

cnf(c_10611,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10599,c_21])).

cnf(c_10612,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_10611])).

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
% 0.12/0.33  % DateTime   : Tue Dec  1 09:39:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 4.07/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/0.99  
% 4.07/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.07/0.99  
% 4.07/0.99  ------  iProver source info
% 4.07/0.99  
% 4.07/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.07/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.07/0.99  git: non_committed_changes: false
% 4.07/0.99  git: last_make_outside_of_git: false
% 4.07/0.99  
% 4.07/0.99  ------ 
% 4.07/0.99  ------ Parsing...
% 4.07/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.07/0.99  
% 4.07/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 4.07/0.99  
% 4.07/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.07/0.99  
% 4.07/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.07/0.99  ------ Proving...
% 4.07/0.99  ------ Problem Properties 
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  clauses                                 27
% 4.07/0.99  conjectures                             6
% 4.07/0.99  EPR                                     7
% 4.07/0.99  Horn                                    16
% 4.07/0.99  unary                                   8
% 4.07/0.99  binary                                  3
% 4.07/0.99  lits                                    110
% 4.07/0.99  lits eq                                 11
% 4.07/0.99  fd_pure                                 0
% 4.07/0.99  fd_pseudo                               0
% 4.07/0.99  fd_cond                                 3
% 4.07/0.99  fd_pseudo_cond                          1
% 4.07/0.99  AC symbols                              0
% 4.07/0.99  
% 4.07/0.99  ------ Input Options Time Limit: Unbounded
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  ------ 
% 4.07/0.99  Current options:
% 4.07/0.99  ------ 
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  ------ Proving...
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  % SZS status Theorem for theBenchmark.p
% 4.07/0.99  
% 4.07/0.99   Resolution empty clause
% 4.07/0.99  
% 4.07/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.07/0.99  
% 4.07/0.99  fof(f6,axiom,(
% 4.07/0.99    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f20,plain,(
% 4.07/0.99    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 4.07/0.99    inference(ennf_transformation,[],[f6])).
% 4.07/0.99  
% 4.07/0.99  fof(f32,plain,(
% 4.07/0.99    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 4.07/0.99    introduced(choice_axiom,[])).
% 4.07/0.99  
% 4.07/0.99  fof(f33,plain,(
% 4.07/0.99    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 4.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f32])).
% 4.07/0.99  
% 4.07/0.99  fof(f48,plain,(
% 4.07/0.99    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 4.07/0.99    inference(cnf_transformation,[],[f33])).
% 4.07/0.99  
% 4.07/0.99  fof(f2,axiom,(
% 4.07/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f44,plain,(
% 4.07/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 4.07/0.99    inference(cnf_transformation,[],[f2])).
% 4.07/0.99  
% 4.07/0.99  fof(f1,axiom,(
% 4.07/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f43,plain,(
% 4.07/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 4.07/0.99    inference(cnf_transformation,[],[f1])).
% 4.07/0.99  
% 4.07/0.99  fof(f13,conjecture,(
% 4.07/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f14,negated_conjecture,(
% 4.07/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 4.07/0.99    inference(negated_conjecture,[],[f13])).
% 4.07/0.99  
% 4.07/0.99  fof(f30,plain,(
% 4.07/0.99    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 4.07/0.99    inference(ennf_transformation,[],[f14])).
% 4.07/0.99  
% 4.07/0.99  fof(f31,plain,(
% 4.07/0.99    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 4.07/0.99    inference(flattening,[],[f30])).
% 4.07/0.99  
% 4.07/0.99  fof(f41,plain,(
% 4.07/0.99    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 4.07/0.99    introduced(choice_axiom,[])).
% 4.07/0.99  
% 4.07/0.99  fof(f42,plain,(
% 4.07/0.99    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 4.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f41])).
% 4.07/0.99  
% 4.07/0.99  fof(f68,plain,(
% 4.07/0.99    l1_orders_2(sK3)),
% 4.07/0.99    inference(cnf_transformation,[],[f42])).
% 4.07/0.99  
% 4.07/0.99  fof(f11,axiom,(
% 4.07/0.99    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f27,plain,(
% 4.07/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 4.07/0.99    inference(ennf_transformation,[],[f11])).
% 4.07/0.99  
% 4.07/0.99  fof(f57,plain,(
% 4.07/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f27])).
% 4.07/0.99  
% 4.07/0.99  fof(f7,axiom,(
% 4.07/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f21,plain,(
% 4.07/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 4.07/0.99    inference(ennf_transformation,[],[f7])).
% 4.07/0.99  
% 4.07/0.99  fof(f51,plain,(
% 4.07/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f21])).
% 4.07/0.99  
% 4.07/0.99  fof(f9,axiom,(
% 4.07/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f23,plain,(
% 4.07/0.99    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 4.07/0.99    inference(ennf_transformation,[],[f9])).
% 4.07/0.99  
% 4.07/0.99  fof(f24,plain,(
% 4.07/0.99    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 4.07/0.99    inference(flattening,[],[f23])).
% 4.07/0.99  
% 4.07/0.99  fof(f55,plain,(
% 4.07/0.99    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f24])).
% 4.07/0.99  
% 4.07/0.99  fof(f64,plain,(
% 4.07/0.99    ~v2_struct_0(sK3)),
% 4.07/0.99    inference(cnf_transformation,[],[f42])).
% 4.07/0.99  
% 4.07/0.99  fof(f65,plain,(
% 4.07/0.99    v3_orders_2(sK3)),
% 4.07/0.99    inference(cnf_transformation,[],[f42])).
% 4.07/0.99  
% 4.07/0.99  fof(f66,plain,(
% 4.07/0.99    v4_orders_2(sK3)),
% 4.07/0.99    inference(cnf_transformation,[],[f42])).
% 4.07/0.99  
% 4.07/0.99  fof(f67,plain,(
% 4.07/0.99    v5_orders_2(sK3)),
% 4.07/0.99    inference(cnf_transformation,[],[f42])).
% 4.07/0.99  
% 4.07/0.99  fof(f12,axiom,(
% 4.07/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f28,plain,(
% 4.07/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 4.07/0.99    inference(ennf_transformation,[],[f12])).
% 4.07/0.99  
% 4.07/0.99  fof(f29,plain,(
% 4.07/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 4.07/0.99    inference(flattening,[],[f28])).
% 4.07/0.99  
% 4.07/0.99  fof(f36,plain,(
% 4.07/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 4.07/0.99    inference(nnf_transformation,[],[f29])).
% 4.07/0.99  
% 4.07/0.99  fof(f37,plain,(
% 4.07/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 4.07/0.99    inference(rectify,[],[f36])).
% 4.07/0.99  
% 4.07/0.99  fof(f39,plain,(
% 4.07/0.99    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 4.07/0.99    introduced(choice_axiom,[])).
% 4.07/0.99  
% 4.07/0.99  fof(f38,plain,(
% 4.07/0.99    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 4.07/0.99    introduced(choice_axiom,[])).
% 4.07/0.99  
% 4.07/0.99  fof(f40,plain,(
% 4.07/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 4.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f39,f38])).
% 4.07/0.99  
% 4.07/0.99  fof(f59,plain,(
% 4.07/0.99    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f40])).
% 4.07/0.99  
% 4.07/0.99  fof(f58,plain,(
% 4.07/0.99    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f40])).
% 4.07/0.99  
% 4.07/0.99  fof(f3,axiom,(
% 4.07/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f15,plain,(
% 4.07/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 4.07/0.99    inference(ennf_transformation,[],[f3])).
% 4.07/0.99  
% 4.07/0.99  fof(f16,plain,(
% 4.07/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 4.07/0.99    inference(flattening,[],[f15])).
% 4.07/0.99  
% 4.07/0.99  fof(f45,plain,(
% 4.07/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f16])).
% 4.07/0.99  
% 4.07/0.99  fof(f69,plain,(
% 4.07/0.99    k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3))),
% 4.07/0.99    inference(cnf_transformation,[],[f42])).
% 4.07/0.99  
% 4.07/0.99  fof(f60,plain,(
% 4.07/0.99    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f40])).
% 4.07/0.99  
% 4.07/0.99  fof(f4,axiom,(
% 4.07/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f17,plain,(
% 4.07/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 4.07/0.99    inference(ennf_transformation,[],[f4])).
% 4.07/0.99  
% 4.07/0.99  fof(f18,plain,(
% 4.07/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 4.07/0.99    inference(flattening,[],[f17])).
% 4.07/0.99  
% 4.07/0.99  fof(f46,plain,(
% 4.07/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f18])).
% 4.07/0.99  
% 4.07/0.99  fof(f8,axiom,(
% 4.07/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f22,plain,(
% 4.07/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.07/0.99    inference(ennf_transformation,[],[f8])).
% 4.07/0.99  
% 4.07/0.99  fof(f34,plain,(
% 4.07/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.07/0.99    inference(nnf_transformation,[],[f22])).
% 4.07/0.99  
% 4.07/0.99  fof(f35,plain,(
% 4.07/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.07/0.99    inference(flattening,[],[f34])).
% 4.07/0.99  
% 4.07/0.99  fof(f53,plain,(
% 4.07/0.99    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f35])).
% 4.07/0.99  
% 4.07/0.99  fof(f70,plain,(
% 4.07/0.99    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 4.07/0.99    inference(equality_resolution,[],[f53])).
% 4.07/0.99  
% 4.07/0.99  fof(f10,axiom,(
% 4.07/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f25,plain,(
% 4.07/0.99    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 4.07/0.99    inference(ennf_transformation,[],[f10])).
% 4.07/0.99  
% 4.07/0.99  fof(f26,plain,(
% 4.07/0.99    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 4.07/0.99    inference(flattening,[],[f25])).
% 4.07/0.99  
% 4.07/0.99  fof(f56,plain,(
% 4.07/0.99    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f26])).
% 4.07/0.99  
% 4.07/0.99  fof(f5,axiom,(
% 4.07/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 4.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.99  
% 4.07/0.99  fof(f19,plain,(
% 4.07/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 4.07/0.99    inference(ennf_transformation,[],[f5])).
% 4.07/0.99  
% 4.07/0.99  fof(f47,plain,(
% 4.07/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 4.07/0.99    inference(cnf_transformation,[],[f19])).
% 4.07/0.99  
% 4.07/0.99  cnf(c_7,plain,
% 4.07/0.99      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 4.07/0.99      inference(cnf_transformation,[],[f48]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_705,plain,
% 4.07/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1,plain,
% 4.07/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f44]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_711,plain,
% 4.07/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_0,plain,
% 4.07/0.99      ( k2_subset_1(X0) = X0 ),
% 4.07/0.99      inference(cnf_transformation,[],[f43]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_726,plain,
% 4.07/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.07/0.99      inference(light_normalisation,[status(thm)],[c_711,c_0]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_22,negated_conjecture,
% 4.07/0.99      ( l1_orders_2(sK3) ),
% 4.07/0.99      inference(cnf_transformation,[],[f68]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_691,plain,
% 4.07/0.99      ( l1_orders_2(sK3) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_14,plain,
% 4.07/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f57]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_698,plain,
% 4.07/0.99      ( l1_orders_2(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1229,plain,
% 4.07/0.99      ( l1_struct_0(sK3) = iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_691,c_698]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_8,plain,
% 4.07/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f51]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_704,plain,
% 4.07/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | l1_struct_0(X0) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1499,plain,
% 4.07/0.99      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1229,c_704]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_12,plain,
% 4.07/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/0.99      | v2_struct_0(X1)
% 4.07/0.99      | ~ v3_orders_2(X1)
% 4.07/0.99      | ~ v4_orders_2(X1)
% 4.07/0.99      | ~ v5_orders_2(X1)
% 4.07/0.99      | ~ l1_orders_2(X1)
% 4.07/0.99      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f55]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_700,plain,
% 4.07/0.99      ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
% 4.07/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.07/0.99      | v2_struct_0(X0) = iProver_top
% 4.07/0.99      | v3_orders_2(X0) != iProver_top
% 4.07/0.99      | v4_orders_2(X0) != iProver_top
% 4.07/0.99      | v5_orders_2(X0) != iProver_top
% 4.07/0.99      | l1_orders_2(X0) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_3285,plain,
% 4.07/0.99      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 4.07/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | v2_struct_0(sK3) = iProver_top
% 4.07/0.99      | v3_orders_2(sK3) != iProver_top
% 4.07/0.99      | v4_orders_2(sK3) != iProver_top
% 4.07/0.99      | v5_orders_2(sK3) != iProver_top
% 4.07/0.99      | l1_orders_2(sK3) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1499,c_700]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_26,negated_conjecture,
% 4.07/0.99      ( ~ v2_struct_0(sK3) ),
% 4.07/0.99      inference(cnf_transformation,[],[f64]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_27,plain,
% 4.07/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_25,negated_conjecture,
% 4.07/0.99      ( v3_orders_2(sK3) ),
% 4.07/0.99      inference(cnf_transformation,[],[f65]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_28,plain,
% 4.07/0.99      ( v3_orders_2(sK3) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_24,negated_conjecture,
% 4.07/0.99      ( v4_orders_2(sK3) ),
% 4.07/0.99      inference(cnf_transformation,[],[f66]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_29,plain,
% 4.07/0.99      ( v4_orders_2(sK3) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_23,negated_conjecture,
% 4.07/0.99      ( v5_orders_2(sK3) ),
% 4.07/0.99      inference(cnf_transformation,[],[f67]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_30,plain,
% 4.07/0.99      ( v5_orders_2(sK3) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_31,plain,
% 4.07/0.99      ( l1_orders_2(sK3) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_3871,plain,
% 4.07/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0) ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_3285,c_27,c_28,c_29,c_30,c_31]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_3872,plain,
% 4.07/0.99      ( a_2_1_orders_2(sK3,X0) = k2_orders_2(sK3,X0)
% 4.07/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 4.07/0.99      inference(renaming,[status(thm)],[c_3871]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_3879,plain,
% 4.07/0.99      ( a_2_1_orders_2(sK3,k2_struct_0(sK3)) = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_726,c_3872]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_19,plain,
% 4.07/0.99      ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 4.07/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/0.99      | v2_struct_0(X1)
% 4.07/0.99      | ~ v3_orders_2(X1)
% 4.07/0.99      | ~ v4_orders_2(X1)
% 4.07/0.99      | ~ v5_orders_2(X1)
% 4.07/0.99      | ~ l1_orders_2(X1)
% 4.07/0.99      | sK2(X0,X1,X2) = X0 ),
% 4.07/0.99      inference(cnf_transformation,[],[f59]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_693,plain,
% 4.07/0.99      ( sK2(X0,X1,X2) = X0
% 4.07/0.99      | r2_hidden(X0,a_2_1_orders_2(X1,X2)) != iProver_top
% 4.07/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.07/0.99      | v2_struct_0(X1) = iProver_top
% 4.07/0.99      | v3_orders_2(X1) != iProver_top
% 4.07/0.99      | v4_orders_2(X1) != iProver_top
% 4.07/0.99      | v5_orders_2(X1) != iProver_top
% 4.07/0.99      | l1_orders_2(X1) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4220,plain,
% 4.07/0.99      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 4.07/0.99      | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 4.07/0.99      | v2_struct_0(sK3) = iProver_top
% 4.07/0.99      | v3_orders_2(sK3) != iProver_top
% 4.07/0.99      | v4_orders_2(sK3) != iProver_top
% 4.07/0.99      | v5_orders_2(sK3) != iProver_top
% 4.07/0.99      | l1_orders_2(sK3) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_3879,c_693]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4221,plain,
% 4.07/0.99      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 4.07/0.99      | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | v2_struct_0(sK3) = iProver_top
% 4.07/0.99      | v3_orders_2(sK3) != iProver_top
% 4.07/0.99      | v4_orders_2(sK3) != iProver_top
% 4.07/0.99      | v5_orders_2(sK3) != iProver_top
% 4.07/0.99      | l1_orders_2(sK3) != iProver_top ),
% 4.07/0.99      inference(light_normalisation,[status(thm)],[c_4220,c_1499]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4226,plain,
% 4.07/0.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | sK2(X0,sK3,k2_struct_0(sK3)) = X0 ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_4221,c_27,c_28,c_29,c_30,c_31]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4227,plain,
% 4.07/0.99      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 4.07/0.99      | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 4.07/0.99      inference(renaming,[status(thm)],[c_4226]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4235,plain,
% 4.07/0.99      ( sK2(X0,sK3,k2_struct_0(sK3)) = X0
% 4.07/0.99      | r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top ),
% 4.07/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_4227,c_726]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4239,plain,
% 4.07/0.99      ( sK2(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),sK3,k2_struct_0(sK3)) = sK0(k2_orders_2(sK3,k2_struct_0(sK3)))
% 4.07/0.99      | k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_705,c_4235]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_20,plain,
% 4.07/0.99      ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 4.07/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/0.99      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 4.07/0.99      | v2_struct_0(X1)
% 4.07/0.99      | ~ v3_orders_2(X1)
% 4.07/0.99      | ~ v4_orders_2(X1)
% 4.07/0.99      | ~ v5_orders_2(X1)
% 4.07/0.99      | ~ l1_orders_2(X1) ),
% 4.07/0.99      inference(cnf_transformation,[],[f58]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_692,plain,
% 4.07/0.99      ( r2_hidden(X0,a_2_1_orders_2(X1,X2)) != iProver_top
% 4.07/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.07/0.99      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top
% 4.07/0.99      | v2_struct_0(X1) = iProver_top
% 4.07/0.99      | v3_orders_2(X1) != iProver_top
% 4.07/0.99      | v4_orders_2(X1) != iProver_top
% 4.07/0.99      | v5_orders_2(X1) != iProver_top
% 4.07/0.99      | l1_orders_2(X1) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2,plain,
% 4.07/0.99      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 4.07/0.99      inference(cnf_transformation,[],[f45]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_710,plain,
% 4.07/0.99      ( r2_hidden(X0,X1) = iProver_top
% 4.07/0.99      | m1_subset_1(X0,X1) != iProver_top
% 4.07/0.99      | v1_xboole_0(X1) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1467,plain,
% 4.07/0.99      ( r2_hidden(X0,a_2_1_orders_2(X1,X2)) != iProver_top
% 4.07/0.99      | r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) = iProver_top
% 4.07/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.07/0.99      | v2_struct_0(X1) = iProver_top
% 4.07/0.99      | v3_orders_2(X1) != iProver_top
% 4.07/0.99      | v4_orders_2(X1) != iProver_top
% 4.07/0.99      | v5_orders_2(X1) != iProver_top
% 4.07/0.99      | l1_orders_2(X1) != iProver_top
% 4.07/0.99      | v1_xboole_0(u1_struct_0(X1)) = iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_692,c_710]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_9867,plain,
% 4.07/0.99      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 4.07/0.99      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),u1_struct_0(sK3)) = iProver_top
% 4.07/0.99      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 4.07/0.99      | v2_struct_0(sK3) = iProver_top
% 4.07/0.99      | v3_orders_2(sK3) != iProver_top
% 4.07/0.99      | v4_orders_2(sK3) != iProver_top
% 4.07/0.99      | v5_orders_2(sK3) != iProver_top
% 4.07/0.99      | l1_orders_2(sK3) != iProver_top
% 4.07/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_4239,c_1467]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10022,plain,
% 4.07/0.99      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 4.07/0.99      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
% 4.07/0.99      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | v2_struct_0(sK3) = iProver_top
% 4.07/0.99      | v3_orders_2(sK3) != iProver_top
% 4.07/0.99      | v4_orders_2(sK3) != iProver_top
% 4.07/0.99      | v5_orders_2(sK3) != iProver_top
% 4.07/0.99      | l1_orders_2(sK3) != iProver_top
% 4.07/0.99      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 4.07/0.99      inference(light_normalisation,[status(thm)],[c_9867,c_1499,c_3879]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_21,negated_conjecture,
% 4.07/0.99      ( k1_xboole_0 != k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f69]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1007,plain,
% 4.07/0.99      ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3)))
% 4.07/0.99      | k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3)) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1008,plain,
% 4.07/0.99      ( k1_xboole_0 = k2_orders_2(sK3,k2_struct_0(sK3))
% 4.07/0.99      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_1007]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_18,plain,
% 4.07/0.99      ( r2_orders_2(X0,sK2(X1,X0,X2),X3)
% 4.07/0.99      | ~ r2_hidden(X3,X2)
% 4.07/0.99      | ~ r2_hidden(X1,a_2_1_orders_2(X0,X2))
% 4.07/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 4.07/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 4.07/0.99      | v2_struct_0(X0)
% 4.07/0.99      | ~ v3_orders_2(X0)
% 4.07/0.99      | ~ v4_orders_2(X0)
% 4.07/0.99      | ~ v5_orders_2(X0)
% 4.07/0.99      | ~ l1_orders_2(X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f60]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_694,plain,
% 4.07/0.99      ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
% 4.07/0.99      | r2_hidden(X3,X2) != iProver_top
% 4.07/0.99      | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
% 4.07/0.99      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 4.07/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.07/0.99      | v2_struct_0(X0) = iProver_top
% 4.07/0.99      | v3_orders_2(X0) != iProver_top
% 4.07/0.99      | v4_orders_2(X0) != iProver_top
% 4.07/0.99      | v5_orders_2(X0) != iProver_top
% 4.07/0.99      | l1_orders_2(X0) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_3,plain,
% 4.07/0.99      ( ~ r2_hidden(X0,X1)
% 4.07/0.99      | m1_subset_1(X0,X2)
% 4.07/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f46]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_709,plain,
% 4.07/0.99      ( r2_hidden(X0,X1) != iProver_top
% 4.07/0.99      | m1_subset_1(X0,X2) = iProver_top
% 4.07/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_923,plain,
% 4.07/0.99      ( r2_orders_2(X0,sK2(X1,X0,X2),X3) = iProver_top
% 4.07/0.99      | r2_hidden(X3,X2) != iProver_top
% 4.07/0.99      | r2_hidden(X1,a_2_1_orders_2(X0,X2)) != iProver_top
% 4.07/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.07/0.99      | v2_struct_0(X0) = iProver_top
% 4.07/0.99      | v3_orders_2(X0) != iProver_top
% 4.07/0.99      | v4_orders_2(X0) != iProver_top
% 4.07/0.99      | v5_orders_2(X0) != iProver_top
% 4.07/0.99      | l1_orders_2(X0) != iProver_top ),
% 4.07/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_694,c_709]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1616,plain,
% 4.07/0.99      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 4.07/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 4.07/0.99      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
% 4.07/0.99      | v2_struct_0(sK3) = iProver_top
% 4.07/0.99      | v3_orders_2(sK3) != iProver_top
% 4.07/0.99      | v4_orders_2(sK3) != iProver_top
% 4.07/0.99      | v5_orders_2(sK3) != iProver_top
% 4.07/0.99      | l1_orders_2(sK3) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1499,c_692]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1617,plain,
% 4.07/0.99      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 4.07/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
% 4.07/0.99      | v2_struct_0(sK3) = iProver_top
% 4.07/0.99      | v3_orders_2(sK3) != iProver_top
% 4.07/0.99      | v4_orders_2(sK3) != iProver_top
% 4.07/0.99      | v5_orders_2(sK3) != iProver_top
% 4.07/0.99      | l1_orders_2(sK3) != iProver_top ),
% 4.07/0.99      inference(light_normalisation,[status(thm)],[c_1616,c_1499]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1622,plain,
% 4.07/0.99      ( m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
% 4.07/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_1617,c_27,c_28,c_29,c_30,c_31]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1623,plain,
% 4.07/0.99      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 4.07/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top ),
% 4.07/0.99      inference(renaming,[status(thm)],[c_1622]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10,plain,
% 4.07/0.99      ( ~ r2_orders_2(X0,X1,X1)
% 4.07/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.07/0.99      | ~ l1_orders_2(X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f70]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_702,plain,
% 4.07/0.99      ( r2_orders_2(X0,X1,X1) != iProver_top
% 4.07/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 4.07/0.99      | l1_orders_2(X0) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2131,plain,
% 4.07/0.99      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 4.07/0.99      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 4.07/0.99      | l1_orders_2(sK3) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1499,c_702]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2489,plain,
% 4.07/0.99      ( m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 4.07/0.99      | r2_orders_2(sK3,X0,X0) != iProver_top ),
% 4.07/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2131,c_31]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2490,plain,
% 4.07/0.99      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 4.07/0.99      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 4.07/0.99      inference(renaming,[status(thm)],[c_2489]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2497,plain,
% 4.07/0.99      ( r2_orders_2(sK3,sK2(X0,sK3,X1),sK2(X0,sK3,X1)) != iProver_top
% 4.07/0.99      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 4.07/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1623,c_2490]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4608,plain,
% 4.07/0.99      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 4.07/0.99      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 4.07/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 4.07/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | v2_struct_0(sK3) = iProver_top
% 4.07/0.99      | v3_orders_2(sK3) != iProver_top
% 4.07/0.99      | v4_orders_2(sK3) != iProver_top
% 4.07/0.99      | v5_orders_2(sK3) != iProver_top
% 4.07/0.99      | l1_orders_2(sK3) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_923,c_2497]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4641,plain,
% 4.07/0.99      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 4.07/0.99      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 4.07/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | v2_struct_0(sK3) = iProver_top
% 4.07/0.99      | v3_orders_2(sK3) != iProver_top
% 4.07/0.99      | v4_orders_2(sK3) != iProver_top
% 4.07/0.99      | v5_orders_2(sK3) != iProver_top
% 4.07/0.99      | l1_orders_2(sK3) != iProver_top ),
% 4.07/0.99      inference(light_normalisation,[status(thm)],[c_4608,c_1499]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_5250,plain,
% 4.07/0.99      ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 4.07/0.99      | r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_4641,c_27,c_28,c_29,c_30,c_31]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_5251,plain,
% 4.07/0.99      ( r2_hidden(X0,a_2_1_orders_2(sK3,X1)) != iProver_top
% 4.07/0.99      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 4.07/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 4.07/0.99      inference(renaming,[status(thm)],[c_5250]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_9875,plain,
% 4.07/0.99      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 4.07/0.99      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),a_2_1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top
% 4.07/0.99      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_4239,c_5251]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_9931,plain,
% 4.07/0.99      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 4.07/0.99      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) != iProver_top
% 4.07/0.99      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 4.07/0.99      inference(light_normalisation,[status(thm)],[c_9875,c_3879]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_13,plain,
% 4.07/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/0.99      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/0.99      | v2_struct_0(X1)
% 4.07/0.99      | ~ v3_orders_2(X1)
% 4.07/0.99      | ~ v4_orders_2(X1)
% 4.07/0.99      | ~ v5_orders_2(X1)
% 4.07/0.99      | ~ l1_orders_2(X1) ),
% 4.07/0.99      inference(cnf_transformation,[],[f56]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_699,plain,
% 4.07/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.07/0.99      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 4.07/0.99      | v2_struct_0(X1) = iProver_top
% 4.07/0.99      | v3_orders_2(X1) != iProver_top
% 4.07/0.99      | v4_orders_2(X1) != iProver_top
% 4.07/0.99      | v5_orders_2(X1) != iProver_top
% 4.07/0.99      | l1_orders_2(X1) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_3481,plain,
% 4.07/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 4.07/0.99      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 4.07/0.99      | v2_struct_0(sK3) = iProver_top
% 4.07/0.99      | v3_orders_2(sK3) != iProver_top
% 4.07/0.99      | v4_orders_2(sK3) != iProver_top
% 4.07/0.99      | v5_orders_2(sK3) != iProver_top
% 4.07/0.99      | l1_orders_2(sK3) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1499,c_699]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_3555,plain,
% 4.07/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 4.07/0.99      | v2_struct_0(sK3) = iProver_top
% 4.07/0.99      | v3_orders_2(sK3) != iProver_top
% 4.07/0.99      | v4_orders_2(sK3) != iProver_top
% 4.07/0.99      | v5_orders_2(sK3) != iProver_top
% 4.07/0.99      | l1_orders_2(sK3) != iProver_top ),
% 4.07/0.99      inference(light_normalisation,[status(thm)],[c_3481,c_1499]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_3988,plain,
% 4.07/0.99      ( m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 4.07/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_3555,c_27,c_28,c_29,c_30,c_31]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_3989,plain,
% 4.07/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | m1_subset_1(k2_orders_2(sK3,X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 4.07/0.99      inference(renaming,[status(thm)],[c_3988]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_3997,plain,
% 4.07/0.99      ( r2_hidden(X0,k2_orders_2(sK3,X1)) != iProver_top
% 4.07/0.99      | m1_subset_1(X0,k2_struct_0(sK3)) = iProver_top
% 4.07/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_3989,c_709]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4568,plain,
% 4.07/0.99      ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | m1_subset_1(X0,k2_struct_0(sK3)) = iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_726,c_3997]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4973,plain,
% 4.07/0.99      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 4.07/0.99      | m1_subset_1(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_705,c_4568]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_5004,plain,
% 4.07/0.99      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 4.07/0.99      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
% 4.07/0.99      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_4973,c_710]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4,plain,
% 4.07/0.99      ( ~ r2_hidden(X0,X1)
% 4.07/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 4.07/0.99      | ~ v1_xboole_0(X2) ),
% 4.07/0.99      inference(cnf_transformation,[],[f47]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_708,plain,
% 4.07/0.99      ( r2_hidden(X0,X1) != iProver_top
% 4.07/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 4.07/0.99      | v1_xboole_0(X2) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_3998,plain,
% 4.07/0.99      ( r2_hidden(X0,k2_orders_2(sK3,X1)) != iProver_top
% 4.07/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_3989,c_708]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_6846,plain,
% 4.07/0.99      ( r2_hidden(X0,k2_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 4.07/0.99      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_726,c_3998]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_7783,plain,
% 4.07/0.99      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 4.07/0.99      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_705,c_6846]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10370,plain,
% 4.07/0.99      ( r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top
% 4.07/0.99      | k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 4.07/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5004,c_7783]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10371,plain,
% 4.07/0.99      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 4.07/0.99      | r2_hidden(sK0(k2_orders_2(sK3,k2_struct_0(sK3))),k2_struct_0(sK3)) = iProver_top ),
% 4.07/0.99      inference(renaming,[status(thm)],[c_10370]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10593,plain,
% 4.07/0.99      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 4.07/0.99      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_10022,c_21,c_1008,c_7783,c_9935]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10599,plain,
% 4.07/0.99      ( k2_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0 ),
% 4.07/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_10593,c_726]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10611,plain,
% 4.07/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 4.07/0.99      inference(demodulation,[status(thm)],[c_10599,c_21]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10612,plain,
% 4.07/0.99      ( $false ),
% 4.07/0.99      inference(equality_resolution_simp,[status(thm)],[c_10611]) ).
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.07/0.99  
% 4.07/0.99  ------                               Statistics
% 4.07/0.99  
% 4.07/0.99  ------ Selected
% 4.07/0.99  
% 4.07/0.99  total_time:                             0.435
% 4.07/0.99  
%------------------------------------------------------------------------------
