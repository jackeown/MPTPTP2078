%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:06 EST 2020

% Result     : Theorem 39.80s
% Output     : CNFRefutation 39.80s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_12405)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f33,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f49])).

fof(f79,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ( ( r2_hidden(X4,X1)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f40])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,(
    k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
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
    inference(nnf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f35,plain,(
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

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(nnf_transformation,[],[f32])).

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

fof(f71,plain,(
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

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
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

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

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
    inference(nnf_transformation,[],[f25])).

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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f72,plain,(
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

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
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

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK2(X1,X2,X3),X2)
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
      ( r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK2(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_1307,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_27,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_817,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_818,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_817])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_29,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_28,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_26,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_822,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_818,c_30,c_29,c_28,c_26])).

cnf(c_130570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | ~ r2_hidden(X2,k1_orders_2(sK4,X0))
    | X1 != X2 ),
    inference(resolution,[status(thm)],[c_1307,c_822])).

cnf(c_11,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_128032,plain,
    ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_11,c_25])).

cnf(c_130963,plain,
    ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,a_2_0_orders_2(sK4,k2_struct_0(sK4)))
    | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_130570,c_128032])).

cnf(c_18,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_55,plain,
    ( ~ l1_orders_2(sK4)
    | l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_73,plain,
    ( ~ l1_struct_0(sK4)
    | u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1310,plain,
    ( X0 != X1
    | k2_struct_0(X0) = k2_struct_0(X1) ),
    theory(equality)).

cnf(c_1321,plain,
    ( k2_struct_0(sK4) = k2_struct_0(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1310])).

cnf(c_1304,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1329,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_2217,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_4092,plain,
    ( k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2217])).

cnf(c_1305,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_2349,plain,
    ( X0 != X1
    | k2_struct_0(sK4) != X1
    | k2_struct_0(sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_3241,plain,
    ( X0 != k2_struct_0(sK4)
    | k2_struct_0(sK4) = X0
    | k2_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2349])).

cnf(c_5294,plain,
    ( u1_struct_0(sK4) != k2_struct_0(sK4)
    | k2_struct_0(sK4) = u1_struct_0(sK4)
    | k2_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3241])).

cnf(c_5243,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | ~ r2_hidden(X2,k1_orders_2(sK4,X0))
    | X1 != X2 ),
    inference(resolution,[status(thm)],[c_1307,c_822])).

cnf(c_2948,plain,
    ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_11,c_25])).

cnf(c_5592,plain,
    ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,a_2_0_orders_2(sK4,k2_struct_0(sK4)))
    | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_5243,c_2948])).

cnf(c_1309,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2027,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_2216,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2027])).

cnf(c_3720,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | X1 != X0
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2216])).

cnf(c_9398,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | X0 != u1_struct_0(sK4)
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3720])).

cnf(c_22572,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | k2_struct_0(sK4) != u1_struct_0(sK4)
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_9398])).

cnf(c_1308,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_6307,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_1309,c_1308])).

cnf(c_403,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_18,c_12])).

cnf(c_869,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_403,c_26])).

cnf(c_870,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_869])).

cnf(c_17710,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK4)))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_6307,c_870])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_18034,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,k2_struct_0(sK4))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_17710,c_7])).

cnf(c_32276,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_18034,c_870])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2107,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK4)),X0)
    | r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3088,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2107])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3089,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2032,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5157,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2032])).

cnf(c_32379,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32276,c_3088,c_3089,c_5157])).

cnf(c_131186,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK4,k2_struct_0(sK4)))
    | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_130963,c_26,c_55,c_73,c_1321,c_1329,c_3088,c_3089,c_5294,c_5592,c_12405,c_13366])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_730,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3(X2,X1,X0) = X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_731,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | sK3(X1,sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_735,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | sK3(X1,sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_731,c_30,c_29,c_28,c_26])).

cnf(c_131210,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK3(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),sK4,X0),a_2_0_orders_2(sK4,k2_struct_0(sK4)))
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,X0)) ),
    inference(resolution,[status(thm)],[c_131186,c_735])).

cnf(c_1944,plain,
    ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
    | k1_xboole_0 = k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2106,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2352,plain,
    ( ~ m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2106])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2037,plain,
    ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X0)
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
    | ~ r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2353,plain,
    ( ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
    | ~ r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2037])).

cnf(c_2728,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,X0))
    | sK3(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),sK4,X0) = sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_4,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_5,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1856,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1842,plain,
    ( a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_822])).

cnf(c_2294,plain,
    ( a_2_0_orders_2(sK4,k2_subset_1(u1_struct_0(sK4))) = k1_orders_2(sK4,k2_subset_1(u1_struct_0(sK4))) ),
    inference(superposition,[status(thm)],[c_1856,c_1842])).

cnf(c_3058,plain,
    ( k1_orders_2(sK4,k2_subset_1(u1_struct_0(sK4))) = a_2_0_orders_2(sK4,u1_struct_0(sK4)) ),
    inference(superposition,[status(thm)],[c_4,c_2294])).

cnf(c_3184,plain,
    ( k1_orders_2(sK4,k2_subset_1(k2_struct_0(sK4))) = a_2_0_orders_2(sK4,u1_struct_0(sK4)) ),
    inference(superposition,[status(thm)],[c_870,c_3058])).

cnf(c_3187,plain,
    ( a_2_0_orders_2(sK4,u1_struct_0(sK4)) = k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(superposition,[status(thm)],[c_4,c_3184])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_799,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_800,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_799])).

cnf(c_804,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_800,c_30,c_29,c_28,c_26])).

cnf(c_1843,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_3185,plain,
    ( m1_subset_1(a_2_0_orders_2(sK4,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(k2_subset_1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3058,c_1843])).

cnf(c_1988,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1991,plain,
    ( m1_subset_1(k2_subset_1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1988])).

cnf(c_12244,plain,
    ( m1_subset_1(a_2_0_orders_2(sK4,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3185,c_1991])).

cnf(c_12249,plain,
    ( m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3187,c_12244])).

cnf(c_12260,plain,
    ( m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12249])).

cnf(c_2705,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X2)
    | X1 != X2
    | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_1307])).

cnf(c_3288,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
    | X1 != u1_struct_0(sK4)
    | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2705])).

cnf(c_7238,plain,
    ( r2_hidden(X0,k2_struct_0(sK4))
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
    | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4)))
    | k2_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3288])).

cnf(c_21673,plain,
    ( r2_hidden(sK3(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),sK4,X0),k2_struct_0(sK4))
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
    | sK3(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),sK4,X0) != sK1(k1_orders_2(sK4,k2_struct_0(sK4)))
    | k2_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_7238])).

cnf(c_5233,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1307,c_1304])).

cnf(c_9791,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | r2_hidden(sK3(X1,sK4,X0),X2) ),
    inference(resolution,[status(thm)],[c_5233,c_735])).

cnf(c_14,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_874,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_875,plain,
    ( ~ r2_orders_2(sK4,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_874])).

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
    inference(cnf_transformation,[],[f72])).

cnf(c_656,plain,
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

cnf(c_657,plain,
    ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_661,plain,
    ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_657,c_30,c_29,c_28,c_26])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_677,plain,
    ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_661,c_9])).

cnf(c_2495,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
    inference(resolution,[status(thm)],[c_875,c_677])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_709,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_27])).

cnf(c_710,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_714,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_710,c_30,c_29,c_28,c_26])).

cnf(c_916,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,a_2_0_orders_2(sK4,X1))
    | X0 != X2
    | sK3(X3,sK4,X1) != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_677,c_875])).

cnf(c_917,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_916])).

cnf(c_2555,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
    | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2495,c_714,c_917])).

cnf(c_10169,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0)) ),
    inference(resolution,[status(thm)],[c_9791,c_2555])).

cnf(c_5610,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK3(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),sK4,X0),a_2_0_orders_2(sK4,k2_struct_0(sK4)))
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,X0)) ),
    inference(resolution,[status(thm)],[c_5592,c_735])).

cnf(c_86243,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK3(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),sK4,X0),k2_struct_0(sK4))
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,X0)) ),
    inference(resolution,[status(thm)],[c_10169,c_5610])).

cnf(c_132272,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_131210,c_26,c_25,c_55,c_73,c_1321,c_1329,c_1944,c_2352,c_2353,c_2728,c_3088,c_3089,c_3432,c_5157,c_5294,c_12405,c_13366,c_21673,c_86243])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_775,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_776,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,a_2_0_orders_2(sK4,X1))
    | r2_hidden(sK2(sK4,X1,X0),X1)
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_780,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,a_2_0_orders_2(sK4,X1))
    | r2_hidden(sK2(sK4,X1,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_776,c_30,c_29,c_28,c_26])).

cnf(c_128022,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,a_2_0_orders_2(sK4,X1))
    | ~ r1_tarski(X1,sK2(sK4,X1,X0)) ),
    inference(resolution,[status(thm)],[c_10,c_780])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_128475,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,a_2_0_orders_2(sK4,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_128022,c_3])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1935,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2936,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,a_2_0_orders_2(sK4,X1))
    | ~ r1_tarski(X1,sK2(sK4,X1,X0)) ),
    inference(resolution,[status(thm)],[c_10,c_780])).

cnf(c_3210,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,a_2_0_orders_2(sK4,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2936,c_3])).

cnf(c_128818,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,a_2_0_orders_2(sK4,k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_128475,c_1935,c_3210])).

cnf(c_132290,plain,
    ( ~ m1_subset_1(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_132272,c_128818])).

cnf(c_1850,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1852,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2530,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK4,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1843,c_1852])).

cnf(c_7061,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,k1_orders_2(sK4,k2_subset_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1856,c_2530])).

cnf(c_9744,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK4,u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3058,c_7061])).

cnf(c_10066,plain,
    ( a_2_0_orders_2(sK4,u1_struct_0(sK4)) = k1_xboole_0
    | m1_subset_1(sK1(a_2_0_orders_2(sK4,u1_struct_0(sK4))),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1850,c_9744])).

cnf(c_10650,plain,
    ( a_2_0_orders_2(sK4,u1_struct_0(sK4)) = k1_xboole_0
    | m1_subset_1(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3187,c_10066])).

cnf(c_1945,plain,
    ( k1_xboole_0 = k1_orders_2(sK4,k2_struct_0(sK4))
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1944])).

cnf(c_2050,plain,
    ( ~ m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X0))
    | m1_subset_1(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X0)
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2285,plain,
    ( ~ m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
    | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2050])).

cnf(c_2287,plain,
    ( m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4)) = iProver_top
    | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2285])).

cnf(c_3090,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3088])).

cnf(c_3092,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3089])).

cnf(c_2070,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1856])).

cnf(c_2296,plain,
    ( a_2_0_orders_2(sK4,u1_struct_0(sK4)) = k1_orders_2(sK4,u1_struct_0(sK4)) ),
    inference(superposition,[status(thm)],[c_2070,c_1842])).

cnf(c_3312,plain,
    ( k1_orders_2(sK4,u1_struct_0(sK4)) = k1_orders_2(sK4,k2_struct_0(sK4)) ),
    inference(superposition,[status(thm)],[c_3187,c_2296])).

cnf(c_3431,plain,
    ( m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3312,c_1843])).

cnf(c_5158,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5157])).

cnf(c_10792,plain,
    ( m1_subset_1(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10650,c_25,c_1945,c_2287,c_3090,c_3092,c_3431,c_5158])).

cnf(c_10794,plain,
    ( m1_subset_1(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10792])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_132290,c_10794,c_1935])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 39.80/5.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.80/5.53  
% 39.80/5.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.80/5.53  
% 39.80/5.53  ------  iProver source info
% 39.80/5.53  
% 39.80/5.53  git: date: 2020-06-30 10:37:57 +0100
% 39.80/5.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.80/5.53  git: non_committed_changes: false
% 39.80/5.53  git: last_make_outside_of_git: false
% 39.80/5.53  
% 39.80/5.53  ------ 
% 39.80/5.53  ------ Parsing...
% 39.80/5.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.80/5.53  
% 39.80/5.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 39.80/5.53  
% 39.80/5.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.80/5.53  
% 39.80/5.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.80/5.53  ------ Proving...
% 39.80/5.53  ------ Problem Properties 
% 39.80/5.53  
% 39.80/5.53  
% 39.80/5.53  clauses                                 23
% 39.80/5.53  conjectures                             1
% 39.80/5.53  EPR                                     3
% 39.80/5.53  Horn                                    19
% 39.80/5.53  unary                                   6
% 39.80/5.53  binary                                  9
% 39.80/5.53  lits                                    52
% 39.80/5.53  lits eq                                 6
% 39.80/5.53  fd_pure                                 0
% 39.80/5.53  fd_pseudo                               0
% 39.80/5.53  fd_cond                                 1
% 39.80/5.53  fd_pseudo_cond                          0
% 39.80/5.53  AC symbols                              0
% 39.80/5.53  
% 39.80/5.53  ------ Input Options Time Limit: Unbounded
% 39.80/5.53  
% 39.80/5.53  
% 39.80/5.53  ------ 
% 39.80/5.53  Current options:
% 39.80/5.53  ------ 
% 39.80/5.53  
% 39.80/5.53  
% 39.80/5.53  
% 39.80/5.53  
% 39.80/5.53  ------ Proving...
% 39.80/5.53  
% 39.80/5.53  
% 39.80/5.53  % SZS status Theorem for theBenchmark.p
% 39.80/5.53  
% 39.80/5.53  % SZS output start CNFRefutation for theBenchmark.p
% 39.80/5.53  
% 39.80/5.53  fof(f12,axiom,(
% 39.80/5.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 39.80/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.80/5.53  
% 39.80/5.53  fof(f26,plain,(
% 39.80/5.53    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 39.80/5.53    inference(ennf_transformation,[],[f12])).
% 39.80/5.53  
% 39.80/5.53  fof(f27,plain,(
% 39.80/5.53    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 39.80/5.53    inference(flattening,[],[f26])).
% 39.80/5.53  
% 39.80/5.53  fof(f67,plain,(
% 39.80/5.53    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 39.80/5.53    inference(cnf_transformation,[],[f27])).
% 39.80/5.53  
% 39.80/5.53  fof(f16,conjecture,(
% 39.80/5.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 39.80/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.80/5.53  
% 39.80/5.53  fof(f17,negated_conjecture,(
% 39.80/5.53    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 39.80/5.53    inference(negated_conjecture,[],[f16])).
% 39.80/5.53  
% 39.80/5.53  fof(f33,plain,(
% 39.80/5.53    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 39.80/5.53    inference(ennf_transformation,[],[f17])).
% 39.80/5.53  
% 39.80/5.53  fof(f34,plain,(
% 39.80/5.53    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 39.80/5.53    inference(flattening,[],[f33])).
% 39.80/5.53  
% 39.80/5.53  fof(f49,plain,(
% 39.80/5.53    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4))),
% 39.80/5.53    introduced(choice_axiom,[])).
% 39.80/5.53  
% 39.80/5.53  fof(f50,plain,(
% 39.80/5.53    k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4)),
% 39.80/5.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f49])).
% 39.80/5.53  
% 39.80/5.53  fof(f79,plain,(
% 39.80/5.53    v5_orders_2(sK4)),
% 39.80/5.53    inference(cnf_transformation,[],[f50])).
% 39.80/5.53  
% 39.80/5.53  fof(f76,plain,(
% 39.80/5.53    ~v2_struct_0(sK4)),
% 39.80/5.53    inference(cnf_transformation,[],[f50])).
% 39.80/5.53  
% 39.80/5.53  fof(f77,plain,(
% 39.80/5.53    v3_orders_2(sK4)),
% 39.80/5.53    inference(cnf_transformation,[],[f50])).
% 39.80/5.53  
% 39.80/5.53  fof(f78,plain,(
% 39.80/5.53    v4_orders_2(sK4)),
% 39.80/5.53    inference(cnf_transformation,[],[f50])).
% 39.80/5.53  
% 39.80/5.53  fof(f80,plain,(
% 39.80/5.53    l1_orders_2(sK4)),
% 39.80/5.53    inference(cnf_transformation,[],[f50])).
% 39.80/5.53  
% 39.80/5.53  fof(f9,axiom,(
% 39.80/5.53    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ((r2_hidden(X4,X1) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 39.80/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.80/5.53  
% 39.80/5.53  fof(f18,plain,(
% 39.80/5.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 39.80/5.53    inference(pure_predicate_removal,[],[f9])).
% 39.80/5.53  
% 39.80/5.53  fof(f23,plain,(
% 39.80/5.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 39.80/5.53    inference(ennf_transformation,[],[f18])).
% 39.80/5.53  
% 39.80/5.53  fof(f40,plain,(
% 39.80/5.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 39.80/5.53    introduced(choice_axiom,[])).
% 39.80/5.53  
% 39.80/5.53  fof(f41,plain,(
% 39.80/5.53    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 39.80/5.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f40])).
% 39.80/5.53  
% 39.80/5.53  fof(f62,plain,(
% 39.80/5.53    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 39.80/5.53    inference(cnf_transformation,[],[f41])).
% 39.80/5.53  
% 39.80/5.53  fof(f81,plain,(
% 39.80/5.53    k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4))),
% 39.80/5.53    inference(cnf_transformation,[],[f50])).
% 39.80/5.53  
% 39.80/5.53  fof(f14,axiom,(
% 39.80/5.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 39.80/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.80/5.53  
% 39.80/5.53  fof(f30,plain,(
% 39.80/5.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 39.80/5.53    inference(ennf_transformation,[],[f14])).
% 39.80/5.53  
% 39.80/5.53  fof(f69,plain,(
% 39.80/5.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 39.80/5.53    inference(cnf_transformation,[],[f30])).
% 39.80/5.53  
% 39.80/5.53  fof(f10,axiom,(
% 39.80/5.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 39.80/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.80/5.53  
% 39.80/5.53  fof(f24,plain,(
% 39.80/5.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 39.80/5.53    inference(ennf_transformation,[],[f10])).
% 39.80/5.53  
% 39.80/5.53  fof(f63,plain,(
% 39.80/5.53    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 39.80/5.53    inference(cnf_transformation,[],[f24])).
% 39.80/5.53  
% 39.80/5.53  fof(f6,axiom,(
% 39.80/5.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 39.80/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.80/5.53  
% 39.80/5.53  fof(f39,plain,(
% 39.80/5.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 39.80/5.53    inference(nnf_transformation,[],[f6])).
% 39.80/5.53  
% 39.80/5.53  fof(f59,plain,(
% 39.80/5.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 39.80/5.53    inference(cnf_transformation,[],[f39])).
% 39.80/5.53  
% 39.80/5.53  fof(f1,axiom,(
% 39.80/5.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 39.80/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.80/5.53  
% 39.80/5.53  fof(f19,plain,(
% 39.80/5.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 39.80/5.53    inference(ennf_transformation,[],[f1])).
% 39.80/5.53  
% 39.80/5.53  fof(f35,plain,(
% 39.80/5.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 39.80/5.53    inference(nnf_transformation,[],[f19])).
% 39.80/5.53  
% 39.80/5.53  fof(f36,plain,(
% 39.80/5.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 39.80/5.53    inference(rectify,[],[f35])).
% 39.80/5.53  
% 39.80/5.53  fof(f37,plain,(
% 39.80/5.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 39.80/5.53    introduced(choice_axiom,[])).
% 39.80/5.53  
% 39.80/5.53  fof(f38,plain,(
% 39.80/5.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 39.80/5.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 39.80/5.53  
% 39.80/5.53  fof(f52,plain,(
% 39.80/5.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 39.80/5.53    inference(cnf_transformation,[],[f38])).
% 39.80/5.53  
% 39.80/5.53  fof(f53,plain,(
% 39.80/5.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 39.80/5.53    inference(cnf_transformation,[],[f38])).
% 39.80/5.53  
% 39.80/5.53  fof(f15,axiom,(
% 39.80/5.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 39.80/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.80/5.53  
% 39.80/5.53  fof(f31,plain,(
% 39.80/5.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 39.80/5.53    inference(ennf_transformation,[],[f15])).
% 39.80/5.53  
% 39.80/5.53  fof(f32,plain,(
% 39.80/5.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 39.80/5.53    inference(flattening,[],[f31])).
% 39.80/5.53  
% 39.80/5.53  fof(f44,plain,(
% 39.80/5.53    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 39.80/5.53    inference(nnf_transformation,[],[f32])).
% 39.80/5.53  
% 39.80/5.53  fof(f45,plain,(
% 39.80/5.53    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 39.80/5.53    inference(rectify,[],[f44])).
% 39.80/5.53  
% 39.80/5.53  fof(f47,plain,(
% 39.80/5.53    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK3(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 39.80/5.53    introduced(choice_axiom,[])).
% 39.80/5.53  
% 39.80/5.53  fof(f46,plain,(
% 39.80/5.53    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK2(X1,X2,X3),X3) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))))),
% 39.80/5.53    introduced(choice_axiom,[])).
% 39.80/5.53  
% 39.80/5.53  fof(f48,plain,(
% 39.80/5.53    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK2(X1,X2,X3),X3) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK3(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 39.80/5.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f45,f47,f46])).
% 39.80/5.53  
% 39.80/5.53  fof(f71,plain,(
% 39.80/5.53    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 39.80/5.53    inference(cnf_transformation,[],[f48])).
% 39.80/5.53  
% 39.80/5.53  fof(f58,plain,(
% 39.80/5.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 39.80/5.53    inference(cnf_transformation,[],[f39])).
% 39.80/5.53  
% 39.80/5.53  fof(f51,plain,(
% 39.80/5.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 39.80/5.53    inference(cnf_transformation,[],[f38])).
% 39.80/5.53  
% 39.80/5.53  fof(f3,axiom,(
% 39.80/5.53    ! [X0] : k2_subset_1(X0) = X0),
% 39.80/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.80/5.53  
% 39.80/5.53  fof(f55,plain,(
% 39.80/5.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 39.80/5.53    inference(cnf_transformation,[],[f3])).
% 39.80/5.53  
% 39.80/5.53  fof(f4,axiom,(
% 39.80/5.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 39.80/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.80/5.53  
% 39.80/5.53  fof(f56,plain,(
% 39.80/5.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 39.80/5.53    inference(cnf_transformation,[],[f4])).
% 39.80/5.53  
% 39.80/5.53  fof(f13,axiom,(
% 39.80/5.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 39.80/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.80/5.53  
% 39.80/5.53  fof(f28,plain,(
% 39.80/5.53    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 39.80/5.53    inference(ennf_transformation,[],[f13])).
% 39.80/5.53  
% 39.80/5.53  fof(f29,plain,(
% 39.80/5.53    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 39.80/5.53    inference(flattening,[],[f28])).
% 39.80/5.53  
% 39.80/5.53  fof(f68,plain,(
% 39.80/5.53    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 39.80/5.53    inference(cnf_transformation,[],[f29])).
% 39.80/5.53  
% 39.80/5.53  fof(f11,axiom,(
% 39.80/5.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 39.80/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.80/5.53  
% 39.80/5.53  fof(f25,plain,(
% 39.80/5.53    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 39.80/5.53    inference(ennf_transformation,[],[f11])).
% 39.80/5.53  
% 39.80/5.53  fof(f42,plain,(
% 39.80/5.53    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 39.80/5.53    inference(nnf_transformation,[],[f25])).
% 39.80/5.53  
% 39.80/5.53  fof(f43,plain,(
% 39.80/5.53    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 39.80/5.53    inference(flattening,[],[f42])).
% 39.80/5.53  
% 39.80/5.53  fof(f65,plain,(
% 39.80/5.53    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 39.80/5.53    inference(cnf_transformation,[],[f43])).
% 39.80/5.53  
% 39.80/5.53  fof(f82,plain,(
% 39.80/5.53    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 39.80/5.53    inference(equality_resolution,[],[f65])).
% 39.80/5.53  
% 39.80/5.53  fof(f72,plain,(
% 39.80/5.53    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK3(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 39.80/5.53    inference(cnf_transformation,[],[f48])).
% 39.80/5.53  
% 39.80/5.53  fof(f7,axiom,(
% 39.80/5.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 39.80/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.80/5.53  
% 39.80/5.53  fof(f20,plain,(
% 39.80/5.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 39.80/5.53    inference(ennf_transformation,[],[f7])).
% 39.80/5.53  
% 39.80/5.53  fof(f21,plain,(
% 39.80/5.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 39.80/5.53    inference(flattening,[],[f20])).
% 39.80/5.53  
% 39.80/5.53  fof(f60,plain,(
% 39.80/5.53    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 39.80/5.53    inference(cnf_transformation,[],[f21])).
% 39.80/5.53  
% 39.80/5.53  fof(f70,plain,(
% 39.80/5.53    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 39.80/5.53    inference(cnf_transformation,[],[f48])).
% 39.80/5.53  
% 39.80/5.53  fof(f8,axiom,(
% 39.80/5.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 39.80/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.80/5.53  
% 39.80/5.53  fof(f22,plain,(
% 39.80/5.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 39.80/5.53    inference(ennf_transformation,[],[f8])).
% 39.80/5.53  
% 39.80/5.53  fof(f61,plain,(
% 39.80/5.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 39.80/5.53    inference(cnf_transformation,[],[f22])).
% 39.80/5.53  
% 39.80/5.53  fof(f74,plain,(
% 39.80/5.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | r2_hidden(sK2(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 39.80/5.53    inference(cnf_transformation,[],[f48])).
% 39.80/5.53  
% 39.80/5.53  fof(f84,plain,(
% 39.80/5.53    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_0_orders_2(X1,X2)) | r2_hidden(sK2(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 39.80/5.53    inference(equality_resolution,[],[f74])).
% 39.80/5.53  
% 39.80/5.53  fof(f2,axiom,(
% 39.80/5.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 39.80/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.80/5.53  
% 39.80/5.53  fof(f54,plain,(
% 39.80/5.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 39.80/5.53    inference(cnf_transformation,[],[f2])).
% 39.80/5.53  
% 39.80/5.53  fof(f5,axiom,(
% 39.80/5.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 39.80/5.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.80/5.53  
% 39.80/5.53  fof(f57,plain,(
% 39.80/5.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 39.80/5.53    inference(cnf_transformation,[],[f5])).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1307,plain,
% 39.80/5.53      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.80/5.53      theory(equality) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_16,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.80/5.53      | v2_struct_0(X1)
% 39.80/5.53      | ~ v3_orders_2(X1)
% 39.80/5.53      | ~ v4_orders_2(X1)
% 39.80/5.53      | ~ v5_orders_2(X1)
% 39.80/5.53      | ~ l1_orders_2(X1)
% 39.80/5.53      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 39.80/5.53      inference(cnf_transformation,[],[f67]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_27,negated_conjecture,
% 39.80/5.53      ( v5_orders_2(sK4) ),
% 39.80/5.53      inference(cnf_transformation,[],[f79]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_817,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.80/5.53      | v2_struct_0(X1)
% 39.80/5.53      | ~ v3_orders_2(X1)
% 39.80/5.53      | ~ v4_orders_2(X1)
% 39.80/5.53      | ~ l1_orders_2(X1)
% 39.80/5.53      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
% 39.80/5.53      | sK4 != X1 ),
% 39.80/5.53      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_818,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | v2_struct_0(sK4)
% 39.80/5.53      | ~ v3_orders_2(sK4)
% 39.80/5.53      | ~ v4_orders_2(sK4)
% 39.80/5.53      | ~ l1_orders_2(sK4)
% 39.80/5.53      | a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0) ),
% 39.80/5.53      inference(unflattening,[status(thm)],[c_817]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_30,negated_conjecture,
% 39.80/5.53      ( ~ v2_struct_0(sK4) ),
% 39.80/5.53      inference(cnf_transformation,[],[f76]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_29,negated_conjecture,
% 39.80/5.53      ( v3_orders_2(sK4) ),
% 39.80/5.53      inference(cnf_transformation,[],[f77]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_28,negated_conjecture,
% 39.80/5.53      ( v4_orders_2(sK4) ),
% 39.80/5.53      inference(cnf_transformation,[],[f78]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_26,negated_conjecture,
% 39.80/5.53      ( l1_orders_2(sK4) ),
% 39.80/5.53      inference(cnf_transformation,[],[f80]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_822,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0) ),
% 39.80/5.53      inference(global_propositional_subsumption,
% 39.80/5.53                [status(thm)],
% 39.80/5.53                [c_818,c_30,c_29,c_28,c_26]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_130570,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.80/5.53      | ~ r2_hidden(X2,k1_orders_2(sK4,X0))
% 39.80/5.53      | X1 != X2 ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_1307,c_822]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_11,plain,
% 39.80/5.53      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 39.80/5.53      inference(cnf_transformation,[],[f62]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_25,negated_conjecture,
% 39.80/5.53      ( k1_xboole_0 != k1_orders_2(sK4,k2_struct_0(sK4)) ),
% 39.80/5.53      inference(cnf_transformation,[],[f81]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_128032,plain,
% 39.80/5.53      ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_11,c_25]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_130963,plain,
% 39.80/5.53      ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | r2_hidden(X0,a_2_0_orders_2(sK4,k2_struct_0(sK4)))
% 39.80/5.53      | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_130570,c_128032]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_18,plain,
% 39.80/5.53      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 39.80/5.53      inference(cnf_transformation,[],[f69]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_55,plain,
% 39.80/5.53      ( ~ l1_orders_2(sK4) | l1_struct_0(sK4) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_18]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_12,plain,
% 39.80/5.53      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 39.80/5.53      inference(cnf_transformation,[],[f63]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_73,plain,
% 39.80/5.53      ( ~ l1_struct_0(sK4) | u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_12]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1310,plain,
% 39.80/5.53      ( X0 != X1 | k2_struct_0(X0) = k2_struct_0(X1) ),
% 39.80/5.53      theory(equality) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1321,plain,
% 39.80/5.53      ( k2_struct_0(sK4) = k2_struct_0(sK4) | sK4 != sK4 ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_1310]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1304,plain,( X0 = X0 ),theory(equality) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1329,plain,
% 39.80/5.53      ( sK4 = sK4 ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_1304]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2217,plain,
% 39.80/5.53      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_1304]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_4092,plain,
% 39.80/5.53      ( k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_2217]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1305,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2349,plain,
% 39.80/5.53      ( X0 != X1 | k2_struct_0(sK4) != X1 | k2_struct_0(sK4) = X0 ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_1305]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_3241,plain,
% 39.80/5.53      ( X0 != k2_struct_0(sK4)
% 39.80/5.53      | k2_struct_0(sK4) = X0
% 39.80/5.53      | k2_struct_0(sK4) != k2_struct_0(sK4) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_2349]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_5294,plain,
% 39.80/5.53      ( u1_struct_0(sK4) != k2_struct_0(sK4)
% 39.80/5.53      | k2_struct_0(sK4) = u1_struct_0(sK4)
% 39.80/5.53      | k2_struct_0(sK4) != k2_struct_0(sK4) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_3241]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_5243,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.80/5.53      | ~ r2_hidden(X2,k1_orders_2(sK4,X0))
% 39.80/5.53      | X1 != X2 ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_1307,c_822]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2948,plain,
% 39.80/5.53      ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_11,c_25]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_5592,plain,
% 39.80/5.53      ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | r2_hidden(X0,a_2_0_orders_2(sK4,k2_struct_0(sK4)))
% 39.80/5.53      | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_5243,c_2948]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1309,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.80/5.53      theory(equality) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2027,plain,
% 39.80/5.53      ( m1_subset_1(X0,X1)
% 39.80/5.53      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 39.80/5.53      | X0 != X2
% 39.80/5.53      | X1 != k1_zfmisc_1(X3) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_1309]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2216,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.80/5.53      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 39.80/5.53      | X2 != X0
% 39.80/5.53      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_2027]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_3720,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | X1 != X0
% 39.80/5.53      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_2216]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_9398,plain,
% 39.80/5.53      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | X0 != u1_struct_0(sK4)
% 39.80/5.53      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_3720]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_22572,plain,
% 39.80/5.53      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | k2_struct_0(sK4) != u1_struct_0(sK4)
% 39.80/5.53      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_9398]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1308,plain,
% 39.80/5.53      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 39.80/5.53      theory(equality) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_6307,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.80/5.53      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 39.80/5.53      | X2 != X0
% 39.80/5.53      | X3 != X1 ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_1309,c_1308]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_403,plain,
% 39.80/5.53      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_18,c_12]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_869,plain,
% 39.80/5.53      ( u1_struct_0(X0) = k2_struct_0(X0) | sK4 != X0 ),
% 39.80/5.53      inference(resolution_lifted,[status(thm)],[c_403,c_26]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_870,plain,
% 39.80/5.53      ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 39.80/5.53      inference(unflattening,[status(thm)],[c_869]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_17710,plain,
% 39.80/5.53      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK4)))
% 39.80/5.53      | X0 != X1 ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_6307,c_870]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_7,plain,
% 39.80/5.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.80/5.53      inference(cnf_transformation,[],[f59]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_18034,plain,
% 39.80/5.53      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ r1_tarski(X1,k2_struct_0(sK4))
% 39.80/5.53      | X0 != X1 ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_17710,c_7]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_32276,plain,
% 39.80/5.53      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4)) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_18034,c_870]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1,plain,
% 39.80/5.53      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 39.80/5.53      inference(cnf_transformation,[],[f52]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2107,plain,
% 39.80/5.53      ( r2_hidden(sK0(X0,u1_struct_0(sK4)),X0)
% 39.80/5.53      | r1_tarski(X0,u1_struct_0(sK4)) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_1]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_3088,plain,
% 39.80/5.53      ( r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
% 39.80/5.53      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_2107]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_0,plain,
% 39.80/5.53      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 39.80/5.53      inference(cnf_transformation,[],[f53]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_3089,plain,
% 39.80/5.53      ( ~ r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
% 39.80/5.53      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_0]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2032,plain,
% 39.80/5.53      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_7]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_5157,plain,
% 39.80/5.53      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_2032]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_32379,plain,
% 39.80/5.53      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 39.80/5.53      inference(global_propositional_subsumption,
% 39.80/5.53                [status(thm)],
% 39.80/5.53                [c_32276,c_3088,c_3089,c_5157]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_131186,plain,
% 39.80/5.53      ( r2_hidden(X0,a_2_0_orders_2(sK4,k2_struct_0(sK4)))
% 39.80/5.53      | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 39.80/5.53      inference(global_propositional_subsumption,
% 39.80/5.53                [status(thm)],
% 39.80/5.53                [c_130963,c_26,c_55,c_73,c_1321,c_1329,c_3088,c_3089,
% 39.80/5.53                 c_5294,c_5592,c_12405,c_13366]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_23,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.80/5.53      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 39.80/5.53      | v2_struct_0(X1)
% 39.80/5.53      | ~ v3_orders_2(X1)
% 39.80/5.53      | ~ v4_orders_2(X1)
% 39.80/5.53      | ~ v5_orders_2(X1)
% 39.80/5.53      | ~ l1_orders_2(X1)
% 39.80/5.53      | sK3(X2,X1,X0) = X2 ),
% 39.80/5.53      inference(cnf_transformation,[],[f71]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_730,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.80/5.53      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 39.80/5.53      | v2_struct_0(X1)
% 39.80/5.53      | ~ v3_orders_2(X1)
% 39.80/5.53      | ~ v4_orders_2(X1)
% 39.80/5.53      | ~ l1_orders_2(X1)
% 39.80/5.53      | sK3(X2,X1,X0) = X2
% 39.80/5.53      | sK4 != X1 ),
% 39.80/5.53      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_731,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.80/5.53      | v2_struct_0(sK4)
% 39.80/5.53      | ~ v3_orders_2(sK4)
% 39.80/5.53      | ~ v4_orders_2(sK4)
% 39.80/5.53      | ~ l1_orders_2(sK4)
% 39.80/5.53      | sK3(X1,sK4,X0) = X1 ),
% 39.80/5.53      inference(unflattening,[status(thm)],[c_730]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_735,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.80/5.53      | sK3(X1,sK4,X0) = X1 ),
% 39.80/5.53      inference(global_propositional_subsumption,
% 39.80/5.53                [status(thm)],
% 39.80/5.53                [c_731,c_30,c_29,c_28,c_26]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_131210,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | r2_hidden(sK3(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),sK4,X0),a_2_0_orders_2(sK4,k2_struct_0(sK4)))
% 39.80/5.53      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,X0)) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_131186,c_735]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1944,plain,
% 39.80/5.53      ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
% 39.80/5.53      | k1_xboole_0 = k1_orders_2(sK4,k2_struct_0(sK4)) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_11]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_8,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 39.80/5.53      inference(cnf_transformation,[],[f58]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2106,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | r1_tarski(X0,u1_struct_0(sK4)) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_8]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2352,plain,
% 39.80/5.53      ( ~ m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),u1_struct_0(sK4)) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_2106]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2,plain,
% 39.80/5.53      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 39.80/5.53      inference(cnf_transformation,[],[f51]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2037,plain,
% 39.80/5.53      ( r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X0)
% 39.80/5.53      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
% 39.80/5.53      | ~ r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),X0) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_2]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2353,plain,
% 39.80/5.53      ( ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4)))
% 39.80/5.53      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
% 39.80/5.53      | ~ r1_tarski(k1_orders_2(sK4,k2_struct_0(sK4)),u1_struct_0(sK4)) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_2037]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2728,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,X0))
% 39.80/5.53      | sK3(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),sK4,X0) = sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_735]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_4,plain,
% 39.80/5.53      ( k2_subset_1(X0) = X0 ),
% 39.80/5.53      inference(cnf_transformation,[],[f55]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_5,plain,
% 39.80/5.53      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 39.80/5.53      inference(cnf_transformation,[],[f56]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1856,plain,
% 39.80/5.53      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 39.80/5.53      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1842,plain,
% 39.80/5.53      ( a_2_0_orders_2(sK4,X0) = k1_orders_2(sK4,X0)
% 39.80/5.53      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 39.80/5.53      inference(predicate_to_equality,[status(thm)],[c_822]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2294,plain,
% 39.80/5.53      ( a_2_0_orders_2(sK4,k2_subset_1(u1_struct_0(sK4))) = k1_orders_2(sK4,k2_subset_1(u1_struct_0(sK4))) ),
% 39.80/5.53      inference(superposition,[status(thm)],[c_1856,c_1842]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_3058,plain,
% 39.80/5.53      ( k1_orders_2(sK4,k2_subset_1(u1_struct_0(sK4))) = a_2_0_orders_2(sK4,u1_struct_0(sK4)) ),
% 39.80/5.53      inference(superposition,[status(thm)],[c_4,c_2294]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_3184,plain,
% 39.80/5.53      ( k1_orders_2(sK4,k2_subset_1(k2_struct_0(sK4))) = a_2_0_orders_2(sK4,u1_struct_0(sK4)) ),
% 39.80/5.53      inference(superposition,[status(thm)],[c_870,c_3058]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_3187,plain,
% 39.80/5.53      ( a_2_0_orders_2(sK4,u1_struct_0(sK4)) = k1_orders_2(sK4,k2_struct_0(sK4)) ),
% 39.80/5.53      inference(superposition,[status(thm)],[c_4,c_3184]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_17,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.80/5.53      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 39.80/5.53      | v2_struct_0(X1)
% 39.80/5.53      | ~ v3_orders_2(X1)
% 39.80/5.53      | ~ v4_orders_2(X1)
% 39.80/5.53      | ~ v5_orders_2(X1)
% 39.80/5.53      | ~ l1_orders_2(X1) ),
% 39.80/5.53      inference(cnf_transformation,[],[f68]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_799,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.80/5.53      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 39.80/5.53      | v2_struct_0(X1)
% 39.80/5.53      | ~ v3_orders_2(X1)
% 39.80/5.53      | ~ v4_orders_2(X1)
% 39.80/5.53      | ~ l1_orders_2(X1)
% 39.80/5.53      | sK4 != X1 ),
% 39.80/5.53      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_800,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | v2_struct_0(sK4)
% 39.80/5.53      | ~ v3_orders_2(sK4)
% 39.80/5.53      | ~ v4_orders_2(sK4)
% 39.80/5.53      | ~ l1_orders_2(sK4) ),
% 39.80/5.53      inference(unflattening,[status(thm)],[c_799]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_804,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 39.80/5.53      inference(global_propositional_subsumption,
% 39.80/5.53                [status(thm)],
% 39.80/5.53                [c_800,c_30,c_29,c_28,c_26]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1843,plain,
% 39.80/5.53      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 39.80/5.53      | m1_subset_1(k1_orders_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 39.80/5.53      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_3185,plain,
% 39.80/5.53      ( m1_subset_1(a_2_0_orders_2(sK4,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 39.80/5.53      | m1_subset_1(k2_subset_1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 39.80/5.53      inference(superposition,[status(thm)],[c_3058,c_1843]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1988,plain,
% 39.80/5.53      ( m1_subset_1(k2_subset_1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_5]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1991,plain,
% 39.80/5.53      ( m1_subset_1(k2_subset_1(u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 39.80/5.53      inference(predicate_to_equality,[status(thm)],[c_1988]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_12244,plain,
% 39.80/5.53      ( m1_subset_1(a_2_0_orders_2(sK4,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 39.80/5.53      inference(global_propositional_subsumption,
% 39.80/5.53                [status(thm)],
% 39.80/5.53                [c_3185,c_1991]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_12249,plain,
% 39.80/5.53      ( m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 39.80/5.53      inference(superposition,[status(thm)],[c_3187,c_12244]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_12260,plain,
% 39.80/5.53      ( m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 39.80/5.53      inference(predicate_to_equality_rev,[status(thm)],[c_12249]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2705,plain,
% 39.80/5.53      ( r2_hidden(X0,X1)
% 39.80/5.53      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X2)
% 39.80/5.53      | X1 != X2
% 39.80/5.53      | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_1307]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_3288,plain,
% 39.80/5.53      ( r2_hidden(X0,X1)
% 39.80/5.53      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
% 39.80/5.53      | X1 != u1_struct_0(sK4)
% 39.80/5.53      | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_2705]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_7238,plain,
% 39.80/5.53      ( r2_hidden(X0,k2_struct_0(sK4))
% 39.80/5.53      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
% 39.80/5.53      | X0 != sK1(k1_orders_2(sK4,k2_struct_0(sK4)))
% 39.80/5.53      | k2_struct_0(sK4) != u1_struct_0(sK4) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_3288]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_21673,plain,
% 39.80/5.53      ( r2_hidden(sK3(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),sK4,X0),k2_struct_0(sK4))
% 39.80/5.53      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
% 39.80/5.53      | sK3(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),sK4,X0) != sK1(k1_orders_2(sK4,k2_struct_0(sK4)))
% 39.80/5.53      | k2_struct_0(sK4) != u1_struct_0(sK4) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_7238]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_5233,plain,
% 39.80/5.53      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_1307,c_1304]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_9791,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ r2_hidden(X1,X2)
% 39.80/5.53      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.80/5.53      | r2_hidden(sK3(X1,sK4,X0),X2) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_5233,c_735]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_14,plain,
% 39.80/5.53      ( ~ r2_orders_2(X0,X1,X1)
% 39.80/5.53      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.80/5.53      | ~ l1_orders_2(X0) ),
% 39.80/5.53      inference(cnf_transformation,[],[f82]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_874,plain,
% 39.80/5.53      ( ~ r2_orders_2(X0,X1,X1)
% 39.80/5.53      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.80/5.53      | sK4 != X0 ),
% 39.80/5.53      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_875,plain,
% 39.80/5.53      ( ~ r2_orders_2(sK4,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 39.80/5.53      inference(unflattening,[status(thm)],[c_874]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_22,plain,
% 39.80/5.53      ( r2_orders_2(X0,X1,sK3(X2,X0,X3))
% 39.80/5.53      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.80/5.53      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 39.80/5.53      | ~ r2_hidden(X1,X3)
% 39.80/5.53      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 39.80/5.53      | v2_struct_0(X0)
% 39.80/5.53      | ~ v3_orders_2(X0)
% 39.80/5.53      | ~ v4_orders_2(X0)
% 39.80/5.53      | ~ v5_orders_2(X0)
% 39.80/5.53      | ~ l1_orders_2(X0) ),
% 39.80/5.53      inference(cnf_transformation,[],[f72]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_656,plain,
% 39.80/5.53      ( r2_orders_2(X0,X1,sK3(X2,X0,X3))
% 39.80/5.53      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 39.80/5.53      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 39.80/5.53      | ~ r2_hidden(X1,X3)
% 39.80/5.53      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 39.80/5.53      | v2_struct_0(X0)
% 39.80/5.53      | ~ v3_orders_2(X0)
% 39.80/5.53      | ~ v4_orders_2(X0)
% 39.80/5.53      | ~ l1_orders_2(X0)
% 39.80/5.53      | sK4 != X0 ),
% 39.80/5.53      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_657,plain,
% 39.80/5.53      ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
% 39.80/5.53      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 39.80/5.53      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ r2_hidden(X0,X2)
% 39.80/5.53      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2))
% 39.80/5.53      | v2_struct_0(sK4)
% 39.80/5.53      | ~ v3_orders_2(sK4)
% 39.80/5.53      | ~ v4_orders_2(sK4)
% 39.80/5.53      | ~ l1_orders_2(sK4) ),
% 39.80/5.53      inference(unflattening,[status(thm)],[c_656]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_661,plain,
% 39.80/5.53      ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
% 39.80/5.53      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 39.80/5.53      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ r2_hidden(X0,X2)
% 39.80/5.53      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2)) ),
% 39.80/5.53      inference(global_propositional_subsumption,
% 39.80/5.53                [status(thm)],
% 39.80/5.53                [c_657,c_30,c_29,c_28,c_26]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_9,plain,
% 39.80/5.53      ( m1_subset_1(X0,X1)
% 39.80/5.53      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 39.80/5.53      | ~ r2_hidden(X0,X2) ),
% 39.80/5.53      inference(cnf_transformation,[],[f60]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_677,plain,
% 39.80/5.53      ( r2_orders_2(sK4,X0,sK3(X1,sK4,X2))
% 39.80/5.53      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ r2_hidden(X0,X2)
% 39.80/5.53      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X2)) ),
% 39.80/5.53      inference(forward_subsumption_resolution,[status(thm)],[c_661,c_9]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2495,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
% 39.80/5.53      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.80/5.53      | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_875,c_677]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_24,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.80/5.53      | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
% 39.80/5.53      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 39.80/5.53      | v2_struct_0(X1)
% 39.80/5.53      | ~ v3_orders_2(X1)
% 39.80/5.53      | ~ v4_orders_2(X1)
% 39.80/5.53      | ~ v5_orders_2(X1)
% 39.80/5.53      | ~ l1_orders_2(X1) ),
% 39.80/5.53      inference(cnf_transformation,[],[f70]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_709,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.80/5.53      | m1_subset_1(sK3(X2,X1,X0),u1_struct_0(X1))
% 39.80/5.53      | ~ r2_hidden(X2,a_2_0_orders_2(X1,X0))
% 39.80/5.53      | v2_struct_0(X1)
% 39.80/5.53      | ~ v3_orders_2(X1)
% 39.80/5.53      | ~ v4_orders_2(X1)
% 39.80/5.53      | ~ l1_orders_2(X1)
% 39.80/5.53      | sK4 != X1 ),
% 39.80/5.53      inference(resolution_lifted,[status(thm)],[c_24,c_27]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_710,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
% 39.80/5.53      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.80/5.53      | v2_struct_0(sK4)
% 39.80/5.53      | ~ v3_orders_2(sK4)
% 39.80/5.53      | ~ v4_orders_2(sK4)
% 39.80/5.53      | ~ l1_orders_2(sK4) ),
% 39.80/5.53      inference(unflattening,[status(thm)],[c_709]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_714,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
% 39.80/5.53      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0)) ),
% 39.80/5.53      inference(global_propositional_subsumption,
% 39.80/5.53                [status(thm)],
% 39.80/5.53                [c_710,c_30,c_29,c_28,c_26]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_916,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 39.80/5.53      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ r2_hidden(X2,X1)
% 39.80/5.53      | ~ r2_hidden(X3,a_2_0_orders_2(sK4,X1))
% 39.80/5.53      | X0 != X2
% 39.80/5.53      | sK3(X3,sK4,X1) != X0
% 39.80/5.53      | sK4 != sK4 ),
% 39.80/5.53      inference(resolution_lifted,[status(thm)],[c_677,c_875]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_917,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ m1_subset_1(sK3(X1,sK4,X0),u1_struct_0(sK4))
% 39.80/5.53      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.80/5.53      | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
% 39.80/5.53      inference(unflattening,[status(thm)],[c_916]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2555,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0))
% 39.80/5.53      | ~ r2_hidden(sK3(X1,sK4,X0),X0) ),
% 39.80/5.53      inference(global_propositional_subsumption,
% 39.80/5.53                [status(thm)],
% 39.80/5.53                [c_2495,c_714,c_917]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_10169,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ r2_hidden(X1,X0)
% 39.80/5.53      | ~ r2_hidden(X1,a_2_0_orders_2(sK4,X0)) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_9791,c_2555]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_5610,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | r2_hidden(sK3(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),sK4,X0),a_2_0_orders_2(sK4,k2_struct_0(sK4)))
% 39.80/5.53      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,X0)) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_5592,c_735]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_86243,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ r2_hidden(sK3(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),sK4,X0),k2_struct_0(sK4))
% 39.80/5.53      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,X0)) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_10169,c_5610]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_132272,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),a_2_0_orders_2(sK4,X0)) ),
% 39.80/5.53      inference(global_propositional_subsumption,
% 39.80/5.53                [status(thm)],
% 39.80/5.53                [c_131210,c_26,c_25,c_55,c_73,c_1321,c_1329,c_1944,
% 39.80/5.53                 c_2352,c_2353,c_2728,c_3088,c_3089,c_3432,c_5157,c_5294,
% 39.80/5.53                 c_12405,c_13366,c_21673,c_86243]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_10,plain,
% 39.80/5.53      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 39.80/5.53      inference(cnf_transformation,[],[f61]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_20,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 39.80/5.53      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 39.80/5.53      | r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 39.80/5.53      | r2_hidden(sK2(X1,X2,X0),X2)
% 39.80/5.53      | v2_struct_0(X1)
% 39.80/5.53      | ~ v3_orders_2(X1)
% 39.80/5.53      | ~ v4_orders_2(X1)
% 39.80/5.53      | ~ v5_orders_2(X1)
% 39.80/5.53      | ~ l1_orders_2(X1) ),
% 39.80/5.53      inference(cnf_transformation,[],[f84]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_775,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 39.80/5.53      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 39.80/5.53      | r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 39.80/5.53      | r2_hidden(sK2(X1,X2,X0),X2)
% 39.80/5.53      | v2_struct_0(X1)
% 39.80/5.53      | ~ v3_orders_2(X1)
% 39.80/5.53      | ~ v4_orders_2(X1)
% 39.80/5.53      | ~ l1_orders_2(X1)
% 39.80/5.53      | sK4 != X1 ),
% 39.80/5.53      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_776,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 39.80/5.53      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | r2_hidden(X0,a_2_0_orders_2(sK4,X1))
% 39.80/5.53      | r2_hidden(sK2(sK4,X1,X0),X1)
% 39.80/5.53      | v2_struct_0(sK4)
% 39.80/5.53      | ~ v3_orders_2(sK4)
% 39.80/5.53      | ~ v4_orders_2(sK4)
% 39.80/5.53      | ~ l1_orders_2(sK4) ),
% 39.80/5.53      inference(unflattening,[status(thm)],[c_775]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_780,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 39.80/5.53      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | r2_hidden(X0,a_2_0_orders_2(sK4,X1))
% 39.80/5.53      | r2_hidden(sK2(sK4,X1,X0),X1) ),
% 39.80/5.53      inference(global_propositional_subsumption,
% 39.80/5.53                [status(thm)],
% 39.80/5.53                [c_776,c_30,c_29,c_28,c_26]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_128022,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 39.80/5.53      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | r2_hidden(X0,a_2_0_orders_2(sK4,X1))
% 39.80/5.53      | ~ r1_tarski(X1,sK2(sK4,X1,X0)) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_10,c_780]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_3,plain,
% 39.80/5.53      ( r1_tarski(k1_xboole_0,X0) ),
% 39.80/5.53      inference(cnf_transformation,[],[f54]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_128475,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 39.80/5.53      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | r2_hidden(X0,a_2_0_orders_2(sK4,k1_xboole_0)) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_128022,c_3]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_6,plain,
% 39.80/5.53      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 39.80/5.53      inference(cnf_transformation,[],[f57]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1935,plain,
% 39.80/5.53      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_6]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2936,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 39.80/5.53      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | r2_hidden(X0,a_2_0_orders_2(sK4,X1))
% 39.80/5.53      | ~ r1_tarski(X1,sK2(sK4,X1,X0)) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_10,c_780]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_3210,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 39.80/5.53      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | r2_hidden(X0,a_2_0_orders_2(sK4,k1_xboole_0)) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_2936,c_3]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_128818,plain,
% 39.80/5.53      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 39.80/5.53      | r2_hidden(X0,a_2_0_orders_2(sK4,k1_xboole_0)) ),
% 39.80/5.53      inference(global_propositional_subsumption,
% 39.80/5.53                [status(thm)],
% 39.80/5.53                [c_128475,c_1935,c_3210]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_132290,plain,
% 39.80/5.53      ( ~ m1_subset_1(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
% 39.80/5.53      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 39.80/5.53      inference(resolution,[status(thm)],[c_132272,c_128818]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1850,plain,
% 39.80/5.53      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 39.80/5.53      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1852,plain,
% 39.80/5.53      ( m1_subset_1(X0,X1) = iProver_top
% 39.80/5.53      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 39.80/5.53      | r2_hidden(X0,X2) != iProver_top ),
% 39.80/5.53      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2530,plain,
% 39.80/5.53      ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
% 39.80/5.53      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 39.80/5.53      | r2_hidden(X0,k1_orders_2(sK4,X1)) != iProver_top ),
% 39.80/5.53      inference(superposition,[status(thm)],[c_1843,c_1852]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_7061,plain,
% 39.80/5.53      ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
% 39.80/5.53      | r2_hidden(X0,k1_orders_2(sK4,k2_subset_1(u1_struct_0(sK4)))) != iProver_top ),
% 39.80/5.53      inference(superposition,[status(thm)],[c_1856,c_2530]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_9744,plain,
% 39.80/5.53      ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
% 39.80/5.53      | r2_hidden(X0,a_2_0_orders_2(sK4,u1_struct_0(sK4))) != iProver_top ),
% 39.80/5.53      inference(superposition,[status(thm)],[c_3058,c_7061]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_10066,plain,
% 39.80/5.53      ( a_2_0_orders_2(sK4,u1_struct_0(sK4)) = k1_xboole_0
% 39.80/5.53      | m1_subset_1(sK1(a_2_0_orders_2(sK4,u1_struct_0(sK4))),u1_struct_0(sK4)) = iProver_top ),
% 39.80/5.53      inference(superposition,[status(thm)],[c_1850,c_9744]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_10650,plain,
% 39.80/5.53      ( a_2_0_orders_2(sK4,u1_struct_0(sK4)) = k1_xboole_0
% 39.80/5.53      | m1_subset_1(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4)) = iProver_top ),
% 39.80/5.53      inference(superposition,[status(thm)],[c_3187,c_10066]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_1945,plain,
% 39.80/5.53      ( k1_xboole_0 = k1_orders_2(sK4,k2_struct_0(sK4))
% 39.80/5.53      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) = iProver_top ),
% 39.80/5.53      inference(predicate_to_equality,[status(thm)],[c_1944]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2050,plain,
% 39.80/5.53      ( ~ m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(X0))
% 39.80/5.53      | m1_subset_1(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),X0)
% 39.80/5.53      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_9]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2285,plain,
% 39.80/5.53      ( ~ m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
% 39.80/5.53      | m1_subset_1(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4))
% 39.80/5.53      | ~ r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) ),
% 39.80/5.53      inference(instantiation,[status(thm)],[c_2050]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2287,plain,
% 39.80/5.53      ( m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 39.80/5.53      | m1_subset_1(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4)) = iProver_top
% 39.80/5.53      | r2_hidden(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),k1_orders_2(sK4,k2_struct_0(sK4))) != iProver_top ),
% 39.80/5.53      inference(predicate_to_equality,[status(thm)],[c_2285]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_3090,plain,
% 39.80/5.53      ( r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top
% 39.80/5.53      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
% 39.80/5.53      inference(predicate_to_equality,[status(thm)],[c_3088]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_3092,plain,
% 39.80/5.53      ( r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
% 39.80/5.53      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
% 39.80/5.53      inference(predicate_to_equality,[status(thm)],[c_3089]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2070,plain,
% 39.80/5.53      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 39.80/5.53      inference(superposition,[status(thm)],[c_4,c_1856]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_2296,plain,
% 39.80/5.53      ( a_2_0_orders_2(sK4,u1_struct_0(sK4)) = k1_orders_2(sK4,u1_struct_0(sK4)) ),
% 39.80/5.53      inference(superposition,[status(thm)],[c_2070,c_1842]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_3312,plain,
% 39.80/5.53      ( k1_orders_2(sK4,u1_struct_0(sK4)) = k1_orders_2(sK4,k2_struct_0(sK4)) ),
% 39.80/5.53      inference(superposition,[status(thm)],[c_3187,c_2296]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_3431,plain,
% 39.80/5.53      ( m1_subset_1(k1_orders_2(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 39.80/5.53      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 39.80/5.53      inference(superposition,[status(thm)],[c_3312,c_1843]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_5158,plain,
% 39.80/5.53      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 39.80/5.53      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top ),
% 39.80/5.53      inference(predicate_to_equality,[status(thm)],[c_5157]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_10792,plain,
% 39.80/5.53      ( m1_subset_1(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4)) = iProver_top ),
% 39.80/5.53      inference(global_propositional_subsumption,
% 39.80/5.53                [status(thm)],
% 39.80/5.53                [c_10650,c_25,c_1945,c_2287,c_3090,c_3092,c_3431,c_5158]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(c_10794,plain,
% 39.80/5.53      ( m1_subset_1(sK1(k1_orders_2(sK4,k2_struct_0(sK4))),u1_struct_0(sK4)) ),
% 39.80/5.53      inference(predicate_to_equality_rev,[status(thm)],[c_10792]) ).
% 39.80/5.53  
% 39.80/5.53  cnf(contradiction,plain,
% 39.80/5.53      ( $false ),
% 39.80/5.53      inference(minisat,[status(thm)],[c_132290,c_10794,c_1935]) ).
% 39.80/5.53  
% 39.80/5.53  
% 39.80/5.53  % SZS output end CNFRefutation for theBenchmark.p
% 39.80/5.53  
% 39.80/5.53  ------                               Statistics
% 39.80/5.53  
% 39.80/5.53  ------ Selected
% 39.80/5.53  
% 39.80/5.53  total_time:                             4.846
% 39.80/5.53  
%------------------------------------------------------------------------------
