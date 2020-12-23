%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:33 EST 2020

% Result     : Theorem 1.41s
% Output     : CNFRefutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 200 expanded)
%              Number of clauses        :   48 (  57 expanded)
%              Number of leaves         :   13 (  52 expanded)
%              Depth                    :   19
%              Number of atoms          :  367 (1047 expanded)
%              Number of equality atoms :   81 ( 201 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(sK1,k1_struct_0(sK1),X1)
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k1_xboole_0 != k3_orders_2(sK1,k1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f29,f28])).

fof(f49,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f24])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    k1_xboole_0 != k3_orders_2(sK1,k1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_640,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_641,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_16,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_328,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_orders_2(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_329,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_18,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_17,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_15,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_333,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_329,c_19,c_18,c_17,c_15])).

cnf(c_636,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_333])).

cnf(c_976,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_641,c_636])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_281,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_286,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_282,c_19,c_18,c_17,c_15])).

cnf(c_638,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_644,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1144,plain,
    ( r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_638,c_644])).

cnf(c_1241,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_641,c_1144])).

cnf(c_1325,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
    | k3_orders_2(sK1,X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_976,c_1241])).

cnf(c_1326,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1325])).

cnf(c_1,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_645,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_212,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_213,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_639,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_931,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_645,c_639])).

cnf(c_1338,plain,
    ( k3_orders_2(sK1,k1_xboole_0,X0) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1326,c_931])).

cnf(c_853,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_858,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(c_1514,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | k3_orders_2(sK1,k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1338,c_858])).

cnf(c_1515,plain,
    ( k3_orders_2(sK1,k1_xboole_0,X0) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1514])).

cnf(c_1522,plain,
    ( k3_orders_2(sK1,k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_640,c_1515])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != k3_orders_2(sK1,k1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_9,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_227,plain,
    ( ~ l1_orders_2(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9,c_7])).

cnf(c_372,plain,
    ( k1_struct_0(X0) = k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_227,c_15])).

cnf(c_373,plain,
    ( k1_struct_0(sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_652,plain,
    ( k3_orders_2(sK1,k1_xboole_0,sK2) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13,c_373])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1522,c_652])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.35  % WCLimit    : 600
% 0.12/0.35  % DateTime   : Tue Dec  1 18:28:21 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 1.41/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.41/1.03  
% 1.41/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.41/1.03  
% 1.41/1.03  ------  iProver source info
% 1.41/1.03  
% 1.41/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.41/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.41/1.03  git: non_committed_changes: false
% 1.41/1.03  git: last_make_outside_of_git: false
% 1.41/1.03  
% 1.41/1.03  ------ 
% 1.41/1.03  
% 1.41/1.03  ------ Input Options
% 1.41/1.03  
% 1.41/1.03  --out_options                           all
% 1.41/1.03  --tptp_safe_out                         true
% 1.41/1.03  --problem_path                          ""
% 1.41/1.03  --include_path                          ""
% 1.41/1.03  --clausifier                            res/vclausify_rel
% 1.41/1.03  --clausifier_options                    --mode clausify
% 1.41/1.03  --stdin                                 false
% 1.41/1.03  --stats_out                             all
% 1.41/1.03  
% 1.41/1.03  ------ General Options
% 1.41/1.03  
% 1.41/1.03  --fof                                   false
% 1.41/1.03  --time_out_real                         305.
% 1.41/1.03  --time_out_virtual                      -1.
% 1.41/1.03  --symbol_type_check                     false
% 1.41/1.03  --clausify_out                          false
% 1.41/1.03  --sig_cnt_out                           false
% 1.41/1.03  --trig_cnt_out                          false
% 1.41/1.03  --trig_cnt_out_tolerance                1.
% 1.41/1.03  --trig_cnt_out_sk_spl                   false
% 1.41/1.03  --abstr_cl_out                          false
% 1.41/1.03  
% 1.41/1.03  ------ Global Options
% 1.41/1.03  
% 1.41/1.03  --schedule                              default
% 1.41/1.03  --add_important_lit                     false
% 1.41/1.03  --prop_solver_per_cl                    1000
% 1.41/1.03  --min_unsat_core                        false
% 1.41/1.03  --soft_assumptions                      false
% 1.41/1.03  --soft_lemma_size                       3
% 1.41/1.03  --prop_impl_unit_size                   0
% 1.41/1.03  --prop_impl_unit                        []
% 1.41/1.03  --share_sel_clauses                     true
% 1.41/1.03  --reset_solvers                         false
% 1.41/1.03  --bc_imp_inh                            [conj_cone]
% 1.41/1.03  --conj_cone_tolerance                   3.
% 1.41/1.03  --extra_neg_conj                        none
% 1.41/1.03  --large_theory_mode                     true
% 1.41/1.03  --prolific_symb_bound                   200
% 1.41/1.03  --lt_threshold                          2000
% 1.41/1.03  --clause_weak_htbl                      true
% 1.41/1.03  --gc_record_bc_elim                     false
% 1.41/1.03  
% 1.41/1.03  ------ Preprocessing Options
% 1.41/1.03  
% 1.41/1.03  --preprocessing_flag                    true
% 1.41/1.03  --time_out_prep_mult                    0.1
% 1.41/1.03  --splitting_mode                        input
% 1.41/1.03  --splitting_grd                         true
% 1.41/1.03  --splitting_cvd                         false
% 1.41/1.03  --splitting_cvd_svl                     false
% 1.41/1.03  --splitting_nvd                         32
% 1.41/1.03  --sub_typing                            true
% 1.41/1.03  --prep_gs_sim                           true
% 1.41/1.03  --prep_unflatten                        true
% 1.41/1.03  --prep_res_sim                          true
% 1.41/1.03  --prep_upred                            true
% 1.41/1.03  --prep_sem_filter                       exhaustive
% 1.41/1.03  --prep_sem_filter_out                   false
% 1.41/1.03  --pred_elim                             true
% 1.41/1.03  --res_sim_input                         true
% 1.41/1.03  --eq_ax_congr_red                       true
% 1.41/1.03  --pure_diseq_elim                       true
% 1.41/1.03  --brand_transform                       false
% 1.41/1.03  --non_eq_to_eq                          false
% 1.41/1.03  --prep_def_merge                        true
% 1.41/1.03  --prep_def_merge_prop_impl              false
% 1.41/1.03  --prep_def_merge_mbd                    true
% 1.41/1.03  --prep_def_merge_tr_red                 false
% 1.41/1.03  --prep_def_merge_tr_cl                  false
% 1.41/1.03  --smt_preprocessing                     true
% 1.41/1.03  --smt_ac_axioms                         fast
% 1.41/1.03  --preprocessed_out                      false
% 1.41/1.03  --preprocessed_stats                    false
% 1.41/1.03  
% 1.41/1.03  ------ Abstraction refinement Options
% 1.41/1.03  
% 1.41/1.03  --abstr_ref                             []
% 1.41/1.03  --abstr_ref_prep                        false
% 1.41/1.03  --abstr_ref_until_sat                   false
% 1.41/1.03  --abstr_ref_sig_restrict                funpre
% 1.41/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.41/1.03  --abstr_ref_under                       []
% 1.41/1.03  
% 1.41/1.03  ------ SAT Options
% 1.41/1.03  
% 1.41/1.03  --sat_mode                              false
% 1.41/1.03  --sat_fm_restart_options                ""
% 1.41/1.03  --sat_gr_def                            false
% 1.41/1.03  --sat_epr_types                         true
% 1.41/1.03  --sat_non_cyclic_types                  false
% 1.41/1.03  --sat_finite_models                     false
% 1.41/1.03  --sat_fm_lemmas                         false
% 1.41/1.03  --sat_fm_prep                           false
% 1.41/1.03  --sat_fm_uc_incr                        true
% 1.41/1.03  --sat_out_model                         small
% 1.41/1.03  --sat_out_clauses                       false
% 1.41/1.03  
% 1.41/1.03  ------ QBF Options
% 1.41/1.03  
% 1.41/1.03  --qbf_mode                              false
% 1.41/1.03  --qbf_elim_univ                         false
% 1.41/1.03  --qbf_dom_inst                          none
% 1.41/1.03  --qbf_dom_pre_inst                      false
% 1.41/1.03  --qbf_sk_in                             false
% 1.41/1.03  --qbf_pred_elim                         true
% 1.41/1.03  --qbf_split                             512
% 1.41/1.03  
% 1.41/1.03  ------ BMC1 Options
% 1.41/1.03  
% 1.41/1.03  --bmc1_incremental                      false
% 1.41/1.03  --bmc1_axioms                           reachable_all
% 1.41/1.03  --bmc1_min_bound                        0
% 1.41/1.03  --bmc1_max_bound                        -1
% 1.41/1.03  --bmc1_max_bound_default                -1
% 1.41/1.03  --bmc1_symbol_reachability              true
% 1.41/1.03  --bmc1_property_lemmas                  false
% 1.41/1.03  --bmc1_k_induction                      false
% 1.41/1.03  --bmc1_non_equiv_states                 false
% 1.41/1.03  --bmc1_deadlock                         false
% 1.41/1.03  --bmc1_ucm                              false
% 1.41/1.03  --bmc1_add_unsat_core                   none
% 1.41/1.03  --bmc1_unsat_core_children              false
% 1.41/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.41/1.03  --bmc1_out_stat                         full
% 1.41/1.03  --bmc1_ground_init                      false
% 1.41/1.03  --bmc1_pre_inst_next_state              false
% 1.41/1.03  --bmc1_pre_inst_state                   false
% 1.41/1.03  --bmc1_pre_inst_reach_state             false
% 1.41/1.03  --bmc1_out_unsat_core                   false
% 1.41/1.03  --bmc1_aig_witness_out                  false
% 1.41/1.03  --bmc1_verbose                          false
% 1.41/1.03  --bmc1_dump_clauses_tptp                false
% 1.41/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.41/1.03  --bmc1_dump_file                        -
% 1.41/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.41/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.41/1.03  --bmc1_ucm_extend_mode                  1
% 1.41/1.03  --bmc1_ucm_init_mode                    2
% 1.41/1.03  --bmc1_ucm_cone_mode                    none
% 1.41/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.41/1.03  --bmc1_ucm_relax_model                  4
% 1.41/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.41/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.41/1.03  --bmc1_ucm_layered_model                none
% 1.41/1.03  --bmc1_ucm_max_lemma_size               10
% 1.41/1.03  
% 1.41/1.03  ------ AIG Options
% 1.41/1.03  
% 1.41/1.03  --aig_mode                              false
% 1.41/1.03  
% 1.41/1.03  ------ Instantiation Options
% 1.41/1.03  
% 1.41/1.03  --instantiation_flag                    true
% 1.41/1.03  --inst_sos_flag                         false
% 1.41/1.03  --inst_sos_phase                        true
% 1.41/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.41/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.41/1.03  --inst_lit_sel_side                     num_symb
% 1.41/1.03  --inst_solver_per_active                1400
% 1.41/1.03  --inst_solver_calls_frac                1.
% 1.41/1.03  --inst_passive_queue_type               priority_queues
% 1.41/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.41/1.03  --inst_passive_queues_freq              [25;2]
% 1.41/1.03  --inst_dismatching                      true
% 1.41/1.03  --inst_eager_unprocessed_to_passive     true
% 1.41/1.03  --inst_prop_sim_given                   true
% 1.41/1.03  --inst_prop_sim_new                     false
% 1.41/1.03  --inst_subs_new                         false
% 1.41/1.03  --inst_eq_res_simp                      false
% 1.41/1.03  --inst_subs_given                       false
% 1.41/1.03  --inst_orphan_elimination               true
% 1.41/1.03  --inst_learning_loop_flag               true
% 1.41/1.03  --inst_learning_start                   3000
% 1.41/1.03  --inst_learning_factor                  2
% 1.41/1.03  --inst_start_prop_sim_after_learn       3
% 1.41/1.03  --inst_sel_renew                        solver
% 1.41/1.03  --inst_lit_activity_flag                true
% 1.41/1.03  --inst_restr_to_given                   false
% 1.41/1.03  --inst_activity_threshold               500
% 1.41/1.03  --inst_out_proof                        true
% 1.41/1.03  
% 1.41/1.03  ------ Resolution Options
% 1.41/1.03  
% 1.41/1.03  --resolution_flag                       true
% 1.41/1.03  --res_lit_sel                           adaptive
% 1.41/1.03  --res_lit_sel_side                      none
% 1.41/1.03  --res_ordering                          kbo
% 1.41/1.03  --res_to_prop_solver                    active
% 1.41/1.03  --res_prop_simpl_new                    false
% 1.41/1.03  --res_prop_simpl_given                  true
% 1.41/1.03  --res_passive_queue_type                priority_queues
% 1.41/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.41/1.03  --res_passive_queues_freq               [15;5]
% 1.41/1.03  --res_forward_subs                      full
% 1.41/1.03  --res_backward_subs                     full
% 1.41/1.03  --res_forward_subs_resolution           true
% 1.41/1.03  --res_backward_subs_resolution          true
% 1.41/1.03  --res_orphan_elimination                true
% 1.41/1.03  --res_time_limit                        2.
% 1.41/1.03  --res_out_proof                         true
% 1.41/1.03  
% 1.41/1.03  ------ Superposition Options
% 1.41/1.03  
% 1.41/1.03  --superposition_flag                    true
% 1.41/1.03  --sup_passive_queue_type                priority_queues
% 1.41/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.41/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.41/1.03  --demod_completeness_check              fast
% 1.41/1.03  --demod_use_ground                      true
% 1.41/1.03  --sup_to_prop_solver                    passive
% 1.41/1.03  --sup_prop_simpl_new                    true
% 1.41/1.03  --sup_prop_simpl_given                  true
% 1.41/1.03  --sup_fun_splitting                     false
% 1.41/1.03  --sup_smt_interval                      50000
% 1.41/1.03  
% 1.41/1.03  ------ Superposition Simplification Setup
% 1.41/1.03  
% 1.41/1.03  --sup_indices_passive                   []
% 1.41/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.41/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.41/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.41/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.41/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.41/1.03  --sup_full_bw                           [BwDemod]
% 1.41/1.03  --sup_immed_triv                        [TrivRules]
% 1.41/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.41/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.41/1.03  --sup_immed_bw_main                     []
% 1.41/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.41/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.41/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.41/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.41/1.03  
% 1.41/1.03  ------ Combination Options
% 1.41/1.03  
% 1.41/1.03  --comb_res_mult                         3
% 1.41/1.03  --comb_sup_mult                         2
% 1.41/1.03  --comb_inst_mult                        10
% 1.41/1.03  
% 1.41/1.03  ------ Debug Options
% 1.41/1.03  
% 1.41/1.03  --dbg_backtrace                         false
% 1.41/1.03  --dbg_dump_prop_clauses                 false
% 1.41/1.03  --dbg_dump_prop_clauses_file            -
% 1.41/1.03  --dbg_out_stat                          false
% 1.41/1.03  ------ Parsing...
% 1.41/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.41/1.03  
% 1.41/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.41/1.03  
% 1.41/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.41/1.03  
% 1.41/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.41/1.03  ------ Proving...
% 1.41/1.03  ------ Problem Properties 
% 1.41/1.03  
% 1.41/1.03  
% 1.41/1.03  clauses                                 12
% 1.41/1.03  conjectures                             2
% 1.41/1.03  EPR                                     0
% 1.41/1.03  Horn                                    11
% 1.41/1.03  unary                                   4
% 1.41/1.03  binary                                  2
% 1.41/1.03  lits                                    31
% 1.41/1.03  lits eq                                 7
% 1.41/1.03  fd_pure                                 0
% 1.41/1.03  fd_pseudo                               0
% 1.41/1.03  fd_cond                                 3
% 1.41/1.03  fd_pseudo_cond                          0
% 1.41/1.03  AC symbols                              0
% 1.41/1.03  
% 1.41/1.03  ------ Schedule dynamic 5 is on 
% 1.41/1.03  
% 1.41/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.41/1.03  
% 1.41/1.03  
% 1.41/1.03  ------ 
% 1.41/1.03  Current options:
% 1.41/1.03  ------ 
% 1.41/1.03  
% 1.41/1.03  ------ Input Options
% 1.41/1.03  
% 1.41/1.03  --out_options                           all
% 1.41/1.03  --tptp_safe_out                         true
% 1.41/1.03  --problem_path                          ""
% 1.41/1.03  --include_path                          ""
% 1.41/1.03  --clausifier                            res/vclausify_rel
% 1.41/1.03  --clausifier_options                    --mode clausify
% 1.41/1.03  --stdin                                 false
% 1.41/1.03  --stats_out                             all
% 1.41/1.03  
% 1.41/1.03  ------ General Options
% 1.41/1.03  
% 1.41/1.03  --fof                                   false
% 1.41/1.03  --time_out_real                         305.
% 1.41/1.03  --time_out_virtual                      -1.
% 1.41/1.03  --symbol_type_check                     false
% 1.41/1.03  --clausify_out                          false
% 1.41/1.03  --sig_cnt_out                           false
% 1.41/1.03  --trig_cnt_out                          false
% 1.41/1.03  --trig_cnt_out_tolerance                1.
% 1.41/1.03  --trig_cnt_out_sk_spl                   false
% 1.41/1.03  --abstr_cl_out                          false
% 1.41/1.03  
% 1.41/1.03  ------ Global Options
% 1.41/1.03  
% 1.41/1.03  --schedule                              default
% 1.41/1.03  --add_important_lit                     false
% 1.41/1.03  --prop_solver_per_cl                    1000
% 1.41/1.03  --min_unsat_core                        false
% 1.41/1.03  --soft_assumptions                      false
% 1.41/1.03  --soft_lemma_size                       3
% 1.41/1.03  --prop_impl_unit_size                   0
% 1.41/1.03  --prop_impl_unit                        []
% 1.41/1.03  --share_sel_clauses                     true
% 1.41/1.03  --reset_solvers                         false
% 1.41/1.03  --bc_imp_inh                            [conj_cone]
% 1.41/1.03  --conj_cone_tolerance                   3.
% 1.41/1.03  --extra_neg_conj                        none
% 1.41/1.03  --large_theory_mode                     true
% 1.41/1.03  --prolific_symb_bound                   200
% 1.41/1.03  --lt_threshold                          2000
% 1.41/1.03  --clause_weak_htbl                      true
% 1.41/1.03  --gc_record_bc_elim                     false
% 1.41/1.03  
% 1.41/1.03  ------ Preprocessing Options
% 1.41/1.03  
% 1.41/1.03  --preprocessing_flag                    true
% 1.41/1.03  --time_out_prep_mult                    0.1
% 1.41/1.03  --splitting_mode                        input
% 1.41/1.03  --splitting_grd                         true
% 1.41/1.03  --splitting_cvd                         false
% 1.41/1.03  --splitting_cvd_svl                     false
% 1.41/1.03  --splitting_nvd                         32
% 1.41/1.03  --sub_typing                            true
% 1.41/1.03  --prep_gs_sim                           true
% 1.41/1.03  --prep_unflatten                        true
% 1.41/1.03  --prep_res_sim                          true
% 1.41/1.03  --prep_upred                            true
% 1.41/1.03  --prep_sem_filter                       exhaustive
% 1.41/1.03  --prep_sem_filter_out                   false
% 1.41/1.03  --pred_elim                             true
% 1.41/1.03  --res_sim_input                         true
% 1.41/1.03  --eq_ax_congr_red                       true
% 1.41/1.03  --pure_diseq_elim                       true
% 1.41/1.03  --brand_transform                       false
% 1.41/1.03  --non_eq_to_eq                          false
% 1.41/1.03  --prep_def_merge                        true
% 1.41/1.03  --prep_def_merge_prop_impl              false
% 1.41/1.03  --prep_def_merge_mbd                    true
% 1.41/1.03  --prep_def_merge_tr_red                 false
% 1.41/1.03  --prep_def_merge_tr_cl                  false
% 1.41/1.03  --smt_preprocessing                     true
% 1.41/1.03  --smt_ac_axioms                         fast
% 1.41/1.03  --preprocessed_out                      false
% 1.41/1.03  --preprocessed_stats                    false
% 1.41/1.03  
% 1.41/1.03  ------ Abstraction refinement Options
% 1.41/1.03  
% 1.41/1.03  --abstr_ref                             []
% 1.41/1.03  --abstr_ref_prep                        false
% 1.41/1.03  --abstr_ref_until_sat                   false
% 1.41/1.03  --abstr_ref_sig_restrict                funpre
% 1.41/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.41/1.03  --abstr_ref_under                       []
% 1.41/1.03  
% 1.41/1.03  ------ SAT Options
% 1.41/1.03  
% 1.41/1.03  --sat_mode                              false
% 1.41/1.03  --sat_fm_restart_options                ""
% 1.41/1.03  --sat_gr_def                            false
% 1.41/1.03  --sat_epr_types                         true
% 1.41/1.03  --sat_non_cyclic_types                  false
% 1.41/1.03  --sat_finite_models                     false
% 1.41/1.03  --sat_fm_lemmas                         false
% 1.41/1.03  --sat_fm_prep                           false
% 1.41/1.03  --sat_fm_uc_incr                        true
% 1.41/1.03  --sat_out_model                         small
% 1.41/1.03  --sat_out_clauses                       false
% 1.41/1.03  
% 1.41/1.03  ------ QBF Options
% 1.41/1.03  
% 1.41/1.03  --qbf_mode                              false
% 1.41/1.03  --qbf_elim_univ                         false
% 1.41/1.03  --qbf_dom_inst                          none
% 1.41/1.03  --qbf_dom_pre_inst                      false
% 1.41/1.03  --qbf_sk_in                             false
% 1.41/1.03  --qbf_pred_elim                         true
% 1.41/1.03  --qbf_split                             512
% 1.41/1.03  
% 1.41/1.03  ------ BMC1 Options
% 1.41/1.03  
% 1.41/1.03  --bmc1_incremental                      false
% 1.41/1.03  --bmc1_axioms                           reachable_all
% 1.41/1.03  --bmc1_min_bound                        0
% 1.41/1.03  --bmc1_max_bound                        -1
% 1.41/1.03  --bmc1_max_bound_default                -1
% 1.41/1.03  --bmc1_symbol_reachability              true
% 1.41/1.03  --bmc1_property_lemmas                  false
% 1.41/1.03  --bmc1_k_induction                      false
% 1.41/1.03  --bmc1_non_equiv_states                 false
% 1.41/1.03  --bmc1_deadlock                         false
% 1.41/1.03  --bmc1_ucm                              false
% 1.41/1.03  --bmc1_add_unsat_core                   none
% 1.41/1.03  --bmc1_unsat_core_children              false
% 1.41/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.41/1.03  --bmc1_out_stat                         full
% 1.41/1.03  --bmc1_ground_init                      false
% 1.41/1.03  --bmc1_pre_inst_next_state              false
% 1.41/1.03  --bmc1_pre_inst_state                   false
% 1.41/1.03  --bmc1_pre_inst_reach_state             false
% 1.41/1.03  --bmc1_out_unsat_core                   false
% 1.41/1.03  --bmc1_aig_witness_out                  false
% 1.41/1.03  --bmc1_verbose                          false
% 1.41/1.03  --bmc1_dump_clauses_tptp                false
% 1.41/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.41/1.03  --bmc1_dump_file                        -
% 1.41/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.41/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.41/1.03  --bmc1_ucm_extend_mode                  1
% 1.41/1.03  --bmc1_ucm_init_mode                    2
% 1.41/1.03  --bmc1_ucm_cone_mode                    none
% 1.41/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.41/1.03  --bmc1_ucm_relax_model                  4
% 1.41/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.41/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.41/1.03  --bmc1_ucm_layered_model                none
% 1.41/1.03  --bmc1_ucm_max_lemma_size               10
% 1.41/1.03  
% 1.41/1.03  ------ AIG Options
% 1.41/1.03  
% 1.41/1.03  --aig_mode                              false
% 1.41/1.03  
% 1.41/1.03  ------ Instantiation Options
% 1.41/1.03  
% 1.41/1.03  --instantiation_flag                    true
% 1.41/1.03  --inst_sos_flag                         false
% 1.41/1.03  --inst_sos_phase                        true
% 1.41/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.41/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.41/1.03  --inst_lit_sel_side                     none
% 1.41/1.03  --inst_solver_per_active                1400
% 1.41/1.03  --inst_solver_calls_frac                1.
% 1.41/1.03  --inst_passive_queue_type               priority_queues
% 1.41/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.41/1.03  --inst_passive_queues_freq              [25;2]
% 1.41/1.03  --inst_dismatching                      true
% 1.41/1.03  --inst_eager_unprocessed_to_passive     true
% 1.41/1.03  --inst_prop_sim_given                   true
% 1.41/1.03  --inst_prop_sim_new                     false
% 1.41/1.03  --inst_subs_new                         false
% 1.41/1.03  --inst_eq_res_simp                      false
% 1.41/1.03  --inst_subs_given                       false
% 1.41/1.03  --inst_orphan_elimination               true
% 1.41/1.03  --inst_learning_loop_flag               true
% 1.41/1.03  --inst_learning_start                   3000
% 1.41/1.03  --inst_learning_factor                  2
% 1.41/1.03  --inst_start_prop_sim_after_learn       3
% 1.41/1.03  --inst_sel_renew                        solver
% 1.41/1.03  --inst_lit_activity_flag                true
% 1.41/1.03  --inst_restr_to_given                   false
% 1.41/1.03  --inst_activity_threshold               500
% 1.41/1.03  --inst_out_proof                        true
% 1.41/1.03  
% 1.41/1.03  ------ Resolution Options
% 1.41/1.03  
% 1.41/1.03  --resolution_flag                       false
% 1.41/1.03  --res_lit_sel                           adaptive
% 1.41/1.03  --res_lit_sel_side                      none
% 1.41/1.03  --res_ordering                          kbo
% 1.41/1.03  --res_to_prop_solver                    active
% 1.41/1.03  --res_prop_simpl_new                    false
% 1.41/1.03  --res_prop_simpl_given                  true
% 1.41/1.03  --res_passive_queue_type                priority_queues
% 1.41/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.41/1.03  --res_passive_queues_freq               [15;5]
% 1.41/1.03  --res_forward_subs                      full
% 1.41/1.03  --res_backward_subs                     full
% 1.41/1.03  --res_forward_subs_resolution           true
% 1.41/1.03  --res_backward_subs_resolution          true
% 1.41/1.03  --res_orphan_elimination                true
% 1.41/1.03  --res_time_limit                        2.
% 1.41/1.03  --res_out_proof                         true
% 1.41/1.03  
% 1.41/1.03  ------ Superposition Options
% 1.41/1.03  
% 1.41/1.03  --superposition_flag                    true
% 1.41/1.03  --sup_passive_queue_type                priority_queues
% 1.41/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.41/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.41/1.03  --demod_completeness_check              fast
% 1.41/1.03  --demod_use_ground                      true
% 1.41/1.03  --sup_to_prop_solver                    passive
% 1.41/1.03  --sup_prop_simpl_new                    true
% 1.41/1.03  --sup_prop_simpl_given                  true
% 1.41/1.03  --sup_fun_splitting                     false
% 1.41/1.03  --sup_smt_interval                      50000
% 1.41/1.03  
% 1.41/1.03  ------ Superposition Simplification Setup
% 1.41/1.03  
% 1.41/1.03  --sup_indices_passive                   []
% 1.41/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.41/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.41/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.41/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.41/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.41/1.03  --sup_full_bw                           [BwDemod]
% 1.41/1.03  --sup_immed_triv                        [TrivRules]
% 1.41/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.41/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.41/1.03  --sup_immed_bw_main                     []
% 1.41/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.41/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.41/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.41/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.41/1.03  
% 1.41/1.03  ------ Combination Options
% 1.41/1.03  
% 1.41/1.03  --comb_res_mult                         3
% 1.41/1.03  --comb_sup_mult                         2
% 1.41/1.03  --comb_inst_mult                        10
% 1.41/1.03  
% 1.41/1.03  ------ Debug Options
% 1.41/1.03  
% 1.41/1.03  --dbg_backtrace                         false
% 1.41/1.03  --dbg_dump_prop_clauses                 false
% 1.41/1.03  --dbg_dump_prop_clauses_file            -
% 1.41/1.03  --dbg_out_stat                          false
% 1.41/1.03  
% 1.41/1.03  
% 1.41/1.03  
% 1.41/1.03  
% 1.41/1.03  ------ Proving...
% 1.41/1.03  
% 1.41/1.03  
% 1.41/1.03  % SZS status Theorem for theBenchmark.p
% 1.41/1.03  
% 1.41/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.41/1.03  
% 1.41/1.03  fof(f10,conjecture,(
% 1.41/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 1.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.41/1.03  
% 1.41/1.03  fof(f11,negated_conjecture,(
% 1.41/1.03    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 1.41/1.03    inference(negated_conjecture,[],[f10])).
% 1.41/1.03  
% 1.41/1.03  fof(f22,plain,(
% 1.41/1.03    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.41/1.03    inference(ennf_transformation,[],[f11])).
% 1.41/1.03  
% 1.41/1.03  fof(f23,plain,(
% 1.41/1.03    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.41/1.03    inference(flattening,[],[f22])).
% 1.41/1.03  
% 1.41/1.03  fof(f29,plain,(
% 1.41/1.03    ( ! [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) => (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),sK2) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.41/1.03    introduced(choice_axiom,[])).
% 1.41/1.03  
% 1.41/1.03  fof(f28,plain,(
% 1.41/1.03    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 != k3_orders_2(sK1,k1_struct_0(sK1),X1) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.41/1.03    introduced(choice_axiom,[])).
% 1.41/1.03  
% 1.41/1.03  fof(f30,plain,(
% 1.41/1.03    (k1_xboole_0 != k3_orders_2(sK1,k1_struct_0(sK1),sK2) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 1.41/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f29,f28])).
% 1.41/1.03  
% 1.41/1.03  fof(f49,plain,(
% 1.41/1.03    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.41/1.03    inference(cnf_transformation,[],[f30])).
% 1.41/1.03  
% 1.41/1.03  fof(f5,axiom,(
% 1.41/1.03    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.41/1.03  
% 1.41/1.03  fof(f15,plain,(
% 1.41/1.03    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.41/1.03    inference(ennf_transformation,[],[f5])).
% 1.41/1.03  
% 1.41/1.03  fof(f24,plain,(
% 1.41/1.03    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 1.41/1.03    introduced(choice_axiom,[])).
% 1.41/1.03  
% 1.41/1.03  fof(f25,plain,(
% 1.41/1.03    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 1.41/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f24])).
% 1.41/1.03  
% 1.41/1.03  fof(f35,plain,(
% 1.41/1.03    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.41/1.03    inference(cnf_transformation,[],[f25])).
% 1.41/1.03  
% 1.41/1.03  fof(f9,axiom,(
% 1.41/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 1.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.41/1.03  
% 1.41/1.03  fof(f20,plain,(
% 1.41/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.41/1.03    inference(ennf_transformation,[],[f9])).
% 1.41/1.03  
% 1.41/1.03  fof(f21,plain,(
% 1.41/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.41/1.03    inference(flattening,[],[f20])).
% 1.41/1.03  
% 1.41/1.03  fof(f26,plain,(
% 1.41/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.41/1.03    inference(nnf_transformation,[],[f21])).
% 1.41/1.03  
% 1.41/1.03  fof(f27,plain,(
% 1.41/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.41/1.03    inference(flattening,[],[f26])).
% 1.41/1.03  
% 1.41/1.03  fof(f42,plain,(
% 1.41/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.41/1.03    inference(cnf_transformation,[],[f27])).
% 1.41/1.03  
% 1.41/1.03  fof(f47,plain,(
% 1.41/1.03    v5_orders_2(sK1)),
% 1.41/1.03    inference(cnf_transformation,[],[f30])).
% 1.41/1.03  
% 1.41/1.03  fof(f44,plain,(
% 1.41/1.03    ~v2_struct_0(sK1)),
% 1.41/1.03    inference(cnf_transformation,[],[f30])).
% 1.41/1.03  
% 1.41/1.03  fof(f45,plain,(
% 1.41/1.03    v3_orders_2(sK1)),
% 1.41/1.03    inference(cnf_transformation,[],[f30])).
% 1.41/1.03  
% 1.41/1.03  fof(f46,plain,(
% 1.41/1.03    v4_orders_2(sK1)),
% 1.41/1.03    inference(cnf_transformation,[],[f30])).
% 1.41/1.03  
% 1.41/1.03  fof(f48,plain,(
% 1.41/1.03    l1_orders_2(sK1)),
% 1.41/1.03    inference(cnf_transformation,[],[f30])).
% 1.41/1.03  
% 1.41/1.03  fof(f7,axiom,(
% 1.41/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.41/1.03  
% 1.41/1.03  fof(f17,plain,(
% 1.41/1.03    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.41/1.03    inference(ennf_transformation,[],[f7])).
% 1.41/1.03  
% 1.41/1.03  fof(f18,plain,(
% 1.41/1.03    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.41/1.03    inference(flattening,[],[f17])).
% 1.41/1.03  
% 1.41/1.03  fof(f39,plain,(
% 1.41/1.03    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.41/1.03    inference(cnf_transformation,[],[f18])).
% 1.41/1.03  
% 1.41/1.03  fof(f3,axiom,(
% 1.41/1.03    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.41/1.03  
% 1.41/1.03  fof(f12,plain,(
% 1.41/1.03    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.41/1.03    inference(ennf_transformation,[],[f3])).
% 1.41/1.03  
% 1.41/1.03  fof(f13,plain,(
% 1.41/1.03    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.41/1.03    inference(flattening,[],[f12])).
% 1.41/1.03  
% 1.41/1.03  fof(f33,plain,(
% 1.41/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.41/1.03    inference(cnf_transformation,[],[f13])).
% 1.41/1.03  
% 1.41/1.03  fof(f2,axiom,(
% 1.41/1.03    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.41/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.41/1.04  
% 1.41/1.04  fof(f32,plain,(
% 1.41/1.04    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.41/1.04    inference(cnf_transformation,[],[f2])).
% 1.41/1.04  
% 1.41/1.04  fof(f1,axiom,(
% 1.41/1.04    v1_xboole_0(k1_xboole_0)),
% 1.41/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.41/1.04  
% 1.41/1.04  fof(f31,plain,(
% 1.41/1.04    v1_xboole_0(k1_xboole_0)),
% 1.41/1.04    inference(cnf_transformation,[],[f1])).
% 1.41/1.04  
% 1.41/1.04  fof(f4,axiom,(
% 1.41/1.04    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.41/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.41/1.04  
% 1.41/1.04  fof(f14,plain,(
% 1.41/1.04    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.41/1.04    inference(ennf_transformation,[],[f4])).
% 1.41/1.04  
% 1.41/1.04  fof(f34,plain,(
% 1.41/1.04    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.41/1.04    inference(cnf_transformation,[],[f14])).
% 1.41/1.04  
% 1.41/1.04  fof(f50,plain,(
% 1.41/1.04    k1_xboole_0 != k3_orders_2(sK1,k1_struct_0(sK1),sK2)),
% 1.41/1.04    inference(cnf_transformation,[],[f30])).
% 1.41/1.04  
% 1.41/1.04  fof(f8,axiom,(
% 1.41/1.04    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.41/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.41/1.04  
% 1.41/1.04  fof(f19,plain,(
% 1.41/1.04    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.41/1.04    inference(ennf_transformation,[],[f8])).
% 1.41/1.04  
% 1.41/1.04  fof(f40,plain,(
% 1.41/1.04    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.41/1.04    inference(cnf_transformation,[],[f19])).
% 1.41/1.04  
% 1.41/1.04  fof(f6,axiom,(
% 1.41/1.04    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 1.41/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.41/1.04  
% 1.41/1.04  fof(f16,plain,(
% 1.41/1.04    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.41/1.04    inference(ennf_transformation,[],[f6])).
% 1.41/1.04  
% 1.41/1.04  fof(f38,plain,(
% 1.41/1.04    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.41/1.04    inference(cnf_transformation,[],[f16])).
% 1.41/1.04  
% 1.41/1.04  cnf(c_14,negated_conjecture,
% 1.41/1.04      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.41/1.04      inference(cnf_transformation,[],[f49]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_640,plain,
% 1.41/1.04      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.41/1.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_6,plain,
% 1.41/1.04      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.41/1.04      inference(cnf_transformation,[],[f35]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_641,plain,
% 1.41/1.04      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 1.41/1.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_11,plain,
% 1.41/1.04      ( r2_hidden(X0,X1)
% 1.41/1.04      | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
% 1.41/1.04      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.41/1.04      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 1.41/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.41/1.04      | v2_struct_0(X2)
% 1.41/1.04      | ~ v3_orders_2(X2)
% 1.41/1.04      | ~ v4_orders_2(X2)
% 1.41/1.04      | ~ v5_orders_2(X2)
% 1.41/1.04      | ~ l1_orders_2(X2) ),
% 1.41/1.04      inference(cnf_transformation,[],[f42]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_16,negated_conjecture,
% 1.41/1.04      ( v5_orders_2(sK1) ),
% 1.41/1.04      inference(cnf_transformation,[],[f47]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_328,plain,
% 1.41/1.04      ( r2_hidden(X0,X1)
% 1.41/1.04      | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
% 1.41/1.04      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.41/1.04      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 1.41/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.41/1.04      | v2_struct_0(X2)
% 1.41/1.04      | ~ v3_orders_2(X2)
% 1.41/1.04      | ~ v4_orders_2(X2)
% 1.41/1.04      | ~ l1_orders_2(X2)
% 1.41/1.04      | sK1 != X2 ),
% 1.41/1.04      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_329,plain,
% 1.41/1.04      ( r2_hidden(X0,X1)
% 1.41/1.04      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
% 1.41/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.41/1.04      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.41/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.41/1.04      | v2_struct_0(sK1)
% 1.41/1.04      | ~ v3_orders_2(sK1)
% 1.41/1.04      | ~ v4_orders_2(sK1)
% 1.41/1.04      | ~ l1_orders_2(sK1) ),
% 1.41/1.04      inference(unflattening,[status(thm)],[c_328]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_19,negated_conjecture,
% 1.41/1.04      ( ~ v2_struct_0(sK1) ),
% 1.41/1.04      inference(cnf_transformation,[],[f44]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_18,negated_conjecture,
% 1.41/1.04      ( v3_orders_2(sK1) ),
% 1.41/1.04      inference(cnf_transformation,[],[f45]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_17,negated_conjecture,
% 1.41/1.04      ( v4_orders_2(sK1) ),
% 1.41/1.04      inference(cnf_transformation,[],[f46]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_15,negated_conjecture,
% 1.41/1.04      ( l1_orders_2(sK1) ),
% 1.41/1.04      inference(cnf_transformation,[],[f48]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_333,plain,
% 1.41/1.04      ( r2_hidden(X0,X1)
% 1.41/1.04      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
% 1.41/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.41/1.04      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.41/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.41/1.04      inference(global_propositional_subsumption,
% 1.41/1.04                [status(thm)],
% 1.41/1.04                [c_329,c_19,c_18,c_17,c_15]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_636,plain,
% 1.41/1.04      ( r2_hidden(X0,X1) = iProver_top
% 1.41/1.04      | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
% 1.41/1.04      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 1.41/1.04      | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
% 1.41/1.04      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.41/1.04      inference(predicate_to_equality,[status(thm)],[c_333]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_976,plain,
% 1.41/1.04      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 1.41/1.04      | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
% 1.41/1.04      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 1.41/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.41/1.04      | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) != iProver_top ),
% 1.41/1.04      inference(superposition,[status(thm)],[c_641,c_636]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_8,plain,
% 1.41/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.41/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.41/1.04      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.41/1.04      | v2_struct_0(X1)
% 1.41/1.04      | ~ v3_orders_2(X1)
% 1.41/1.04      | ~ v4_orders_2(X1)
% 1.41/1.04      | ~ v5_orders_2(X1)
% 1.41/1.04      | ~ l1_orders_2(X1) ),
% 1.41/1.04      inference(cnf_transformation,[],[f39]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_281,plain,
% 1.41/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.41/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.41/1.04      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.41/1.04      | v2_struct_0(X1)
% 1.41/1.04      | ~ v3_orders_2(X1)
% 1.41/1.04      | ~ v4_orders_2(X1)
% 1.41/1.04      | ~ l1_orders_2(X1)
% 1.41/1.04      | sK1 != X1 ),
% 1.41/1.04      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_282,plain,
% 1.41/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.41/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.41/1.04      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.41/1.04      | v2_struct_0(sK1)
% 1.41/1.04      | ~ v3_orders_2(sK1)
% 1.41/1.04      | ~ v4_orders_2(sK1)
% 1.41/1.04      | ~ l1_orders_2(sK1) ),
% 1.41/1.04      inference(unflattening,[status(thm)],[c_281]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_286,plain,
% 1.41/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.41/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.41/1.04      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.41/1.04      inference(global_propositional_subsumption,
% 1.41/1.04                [status(thm)],
% 1.41/1.04                [c_282,c_19,c_18,c_17,c_15]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_638,plain,
% 1.41/1.04      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 1.41/1.04      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.41/1.04      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.41/1.04      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_2,plain,
% 1.41/1.04      ( ~ r2_hidden(X0,X1)
% 1.41/1.04      | m1_subset_1(X0,X2)
% 1.41/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 1.41/1.04      inference(cnf_transformation,[],[f33]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_644,plain,
% 1.41/1.04      ( r2_hidden(X0,X1) != iProver_top
% 1.41/1.04      | m1_subset_1(X0,X2) = iProver_top
% 1.41/1.04      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 1.41/1.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_1144,plain,
% 1.41/1.04      ( r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
% 1.41/1.04      | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
% 1.41/1.04      | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
% 1.41/1.04      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.41/1.04      inference(superposition,[status(thm)],[c_638,c_644]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_1241,plain,
% 1.41/1.04      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 1.41/1.04      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 1.41/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.41/1.04      | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) = iProver_top ),
% 1.41/1.04      inference(superposition,[status(thm)],[c_641,c_1144]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_1325,plain,
% 1.41/1.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.41/1.04      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 1.41/1.04      | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
% 1.41/1.04      | k3_orders_2(sK1,X0,X1) = k1_xboole_0 ),
% 1.41/1.04      inference(global_propositional_subsumption,
% 1.41/1.04                [status(thm)],
% 1.41/1.04                [c_976,c_1241]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_1326,plain,
% 1.41/1.04      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 1.41/1.04      | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
% 1.41/1.04      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 1.41/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.41/1.04      inference(renaming,[status(thm)],[c_1325]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_1,plain,
% 1.41/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.41/1.04      inference(cnf_transformation,[],[f32]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_645,plain,
% 1.41/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.41/1.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_0,plain,
% 1.41/1.04      ( v1_xboole_0(k1_xboole_0) ),
% 1.41/1.04      inference(cnf_transformation,[],[f31]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_3,plain,
% 1.41/1.04      ( ~ r2_hidden(X0,X1)
% 1.41/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.41/1.04      | ~ v1_xboole_0(X2) ),
% 1.41/1.04      inference(cnf_transformation,[],[f34]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_212,plain,
% 1.41/1.04      ( ~ r2_hidden(X0,X1)
% 1.41/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.41/1.04      | k1_xboole_0 != X2 ),
% 1.41/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_213,plain,
% 1.41/1.04      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
% 1.41/1.04      inference(unflattening,[status(thm)],[c_212]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_639,plain,
% 1.41/1.04      ( r2_hidden(X0,X1) != iProver_top
% 1.41/1.04      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.41/1.04      inference(predicate_to_equality,[status(thm)],[c_213]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_931,plain,
% 1.41/1.04      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.41/1.04      inference(superposition,[status(thm)],[c_645,c_639]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_1338,plain,
% 1.41/1.04      ( k3_orders_2(sK1,k1_xboole_0,X0) = k1_xboole_0
% 1.41/1.04      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 1.41/1.04      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.41/1.04      inference(superposition,[status(thm)],[c_1326,c_931]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_853,plain,
% 1.41/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.41/1.04      inference(instantiation,[status(thm)],[c_1]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_858,plain,
% 1.41/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.41/1.04      inference(predicate_to_equality,[status(thm)],[c_853]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_1514,plain,
% 1.41/1.04      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 1.41/1.04      | k3_orders_2(sK1,k1_xboole_0,X0) = k1_xboole_0 ),
% 1.41/1.04      inference(global_propositional_subsumption,
% 1.41/1.04                [status(thm)],
% 1.41/1.04                [c_1338,c_858]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_1515,plain,
% 1.41/1.04      ( k3_orders_2(sK1,k1_xboole_0,X0) = k1_xboole_0
% 1.41/1.04      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 1.41/1.04      inference(renaming,[status(thm)],[c_1514]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_1522,plain,
% 1.41/1.04      ( k3_orders_2(sK1,k1_xboole_0,sK2) = k1_xboole_0 ),
% 1.41/1.04      inference(superposition,[status(thm)],[c_640,c_1515]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_13,negated_conjecture,
% 1.41/1.04      ( k1_xboole_0 != k3_orders_2(sK1,k1_struct_0(sK1),sK2) ),
% 1.41/1.04      inference(cnf_transformation,[],[f50]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_9,plain,
% 1.41/1.04      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.41/1.04      inference(cnf_transformation,[],[f40]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_7,plain,
% 1.41/1.04      ( ~ l1_struct_0(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 1.41/1.04      inference(cnf_transformation,[],[f38]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_227,plain,
% 1.41/1.04      ( ~ l1_orders_2(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 1.41/1.04      inference(resolution,[status(thm)],[c_9,c_7]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_372,plain,
% 1.41/1.04      ( k1_struct_0(X0) = k1_xboole_0 | sK1 != X0 ),
% 1.41/1.04      inference(resolution_lifted,[status(thm)],[c_227,c_15]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_373,plain,
% 1.41/1.04      ( k1_struct_0(sK1) = k1_xboole_0 ),
% 1.41/1.04      inference(unflattening,[status(thm)],[c_372]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(c_652,plain,
% 1.41/1.04      ( k3_orders_2(sK1,k1_xboole_0,sK2) != k1_xboole_0 ),
% 1.41/1.04      inference(light_normalisation,[status(thm)],[c_13,c_373]) ).
% 1.41/1.04  
% 1.41/1.04  cnf(contradiction,plain,
% 1.41/1.04      ( $false ),
% 1.41/1.04      inference(minisat,[status(thm)],[c_1522,c_652]) ).
% 1.41/1.04  
% 1.41/1.04  
% 1.41/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 1.41/1.04  
% 1.41/1.04  ------                               Statistics
% 1.41/1.04  
% 1.41/1.04  ------ General
% 1.41/1.04  
% 1.41/1.04  abstr_ref_over_cycles:                  0
% 1.41/1.04  abstr_ref_under_cycles:                 0
% 1.41/1.04  gc_basic_clause_elim:                   0
% 1.41/1.04  forced_gc_time:                         0
% 1.41/1.04  parsing_time:                           0.01
% 1.41/1.04  unif_index_cands_time:                  0.
% 1.41/1.04  unif_index_add_time:                    0.
% 1.41/1.04  orderings_time:                         0.
% 1.41/1.04  out_proof_time:                         0.012
% 1.41/1.04  total_time:                             0.099
% 1.41/1.04  num_of_symbols:                         50
% 1.41/1.04  num_of_terms:                           1480
% 1.41/1.04  
% 1.41/1.04  ------ Preprocessing
% 1.41/1.04  
% 1.41/1.04  num_of_splits:                          0
% 1.41/1.04  num_of_split_atoms:                     0
% 1.41/1.04  num_of_reused_defs:                     0
% 1.41/1.04  num_eq_ax_congr_red:                    13
% 1.41/1.04  num_of_sem_filtered_clauses:            1
% 1.41/1.04  num_of_subtypes:                        0
% 1.41/1.04  monotx_restored_types:                  0
% 1.41/1.04  sat_num_of_epr_types:                   0
% 1.41/1.04  sat_num_of_non_cyclic_types:            0
% 1.41/1.04  sat_guarded_non_collapsed_types:        0
% 1.41/1.04  num_pure_diseq_elim:                    0
% 1.41/1.04  simp_replaced_by:                       0
% 1.41/1.04  res_preprocessed:                       73
% 1.41/1.04  prep_upred:                             0
% 1.41/1.04  prep_unflattend:                        5
% 1.41/1.04  smt_new_axioms:                         0
% 1.41/1.04  pred_elim_cands:                        2
% 1.41/1.04  pred_elim:                              8
% 1.41/1.04  pred_elim_cl:                           8
% 1.41/1.04  pred_elim_cycles:                       10
% 1.41/1.04  merged_defs:                            0
% 1.41/1.04  merged_defs_ncl:                        0
% 1.41/1.04  bin_hyper_res:                          0
% 1.41/1.04  prep_cycles:                            4
% 1.41/1.04  pred_elim_time:                         0.005
% 1.41/1.04  splitting_time:                         0.
% 1.41/1.04  sem_filter_time:                        0.
% 1.41/1.04  monotx_time:                            0.
% 1.41/1.04  subtype_inf_time:                       0.
% 1.41/1.04  
% 1.41/1.04  ------ Problem properties
% 1.41/1.04  
% 1.41/1.04  clauses:                                12
% 1.41/1.04  conjectures:                            2
% 1.41/1.04  epr:                                    0
% 1.41/1.04  horn:                                   11
% 1.41/1.04  ground:                                 3
% 1.41/1.04  unary:                                  4
% 1.41/1.04  binary:                                 2
% 1.41/1.04  lits:                                   31
% 1.41/1.04  lits_eq:                                7
% 1.41/1.04  fd_pure:                                0
% 1.41/1.04  fd_pseudo:                              0
% 1.41/1.04  fd_cond:                                3
% 1.41/1.04  fd_pseudo_cond:                         0
% 1.41/1.04  ac_symbols:                             0
% 1.41/1.04  
% 1.41/1.04  ------ Propositional Solver
% 1.41/1.04  
% 1.41/1.04  prop_solver_calls:                      26
% 1.41/1.04  prop_fast_solver_calls:                 536
% 1.41/1.04  smt_solver_calls:                       0
% 1.41/1.04  smt_fast_solver_calls:                  0
% 1.41/1.04  prop_num_of_clauses:                    500
% 1.41/1.04  prop_preprocess_simplified:             2328
% 1.41/1.04  prop_fo_subsumed:                       14
% 1.41/1.04  prop_solver_time:                       0.
% 1.41/1.04  smt_solver_time:                        0.
% 1.41/1.04  smt_fast_solver_time:                   0.
% 1.41/1.04  prop_fast_solver_time:                  0.
% 1.41/1.04  prop_unsat_core_time:                   0.
% 1.41/1.04  
% 1.41/1.04  ------ QBF
% 1.41/1.04  
% 1.41/1.04  qbf_q_res:                              0
% 1.41/1.04  qbf_num_tautologies:                    0
% 1.41/1.04  qbf_prep_cycles:                        0
% 1.41/1.04  
% 1.41/1.04  ------ BMC1
% 1.41/1.04  
% 1.41/1.04  bmc1_current_bound:                     -1
% 1.41/1.04  bmc1_last_solved_bound:                 -1
% 1.41/1.04  bmc1_unsat_core_size:                   -1
% 1.41/1.04  bmc1_unsat_core_parents_size:           -1
% 1.41/1.04  bmc1_merge_next_fun:                    0
% 1.41/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.41/1.04  
% 1.41/1.04  ------ Instantiation
% 1.41/1.04  
% 1.41/1.04  inst_num_of_clauses:                    148
% 1.41/1.04  inst_num_in_passive:                    8
% 1.41/1.04  inst_num_in_active:                     82
% 1.41/1.04  inst_num_in_unprocessed:                58
% 1.41/1.04  inst_num_of_loops:                      90
% 1.41/1.04  inst_num_of_learning_restarts:          0
% 1.41/1.04  inst_num_moves_active_passive:          6
% 1.41/1.04  inst_lit_activity:                      0
% 1.41/1.04  inst_lit_activity_moves:                0
% 1.41/1.04  inst_num_tautologies:                   0
% 1.41/1.04  inst_num_prop_implied:                  0
% 1.41/1.04  inst_num_existing_simplified:           0
% 1.41/1.04  inst_num_eq_res_simplified:             0
% 1.41/1.04  inst_num_child_elim:                    0
% 1.41/1.04  inst_num_of_dismatching_blockings:      12
% 1.41/1.04  inst_num_of_non_proper_insts:           88
% 1.41/1.04  inst_num_of_duplicates:                 0
% 1.41/1.04  inst_inst_num_from_inst_to_res:         0
% 1.41/1.04  inst_dismatching_checking_time:         0.
% 1.41/1.04  
% 1.41/1.04  ------ Resolution
% 1.41/1.04  
% 1.41/1.04  res_num_of_clauses:                     0
% 1.41/1.04  res_num_in_passive:                     0
% 1.41/1.04  res_num_in_active:                      0
% 1.41/1.04  res_num_of_loops:                       77
% 1.41/1.04  res_forward_subset_subsumed:            11
% 1.41/1.04  res_backward_subset_subsumed:           0
% 1.41/1.04  res_forward_subsumed:                   0
% 1.41/1.04  res_backward_subsumed:                  0
% 1.41/1.04  res_forward_subsumption_resolution:     1
% 1.41/1.04  res_backward_subsumption_resolution:    0
% 1.41/1.04  res_clause_to_clause_subsumption:       145
% 1.41/1.04  res_orphan_elimination:                 0
% 1.41/1.04  res_tautology_del:                      15
% 1.41/1.04  res_num_eq_res_simplified:              0
% 1.41/1.04  res_num_sel_changes:                    0
% 1.41/1.04  res_moves_from_active_to_pass:          0
% 1.41/1.04  
% 1.41/1.04  ------ Superposition
% 1.41/1.04  
% 1.41/1.04  sup_time_total:                         0.
% 1.41/1.04  sup_time_generating:                    0.
% 1.41/1.04  sup_time_sim_full:                      0.
% 1.41/1.04  sup_time_sim_immed:                     0.
% 1.41/1.04  
% 1.41/1.04  sup_num_of_clauses:                     23
% 1.41/1.04  sup_num_in_active:                      18
% 1.41/1.04  sup_num_in_passive:                     5
% 1.41/1.04  sup_num_of_loops:                       17
% 1.41/1.04  sup_fw_superposition:                   6
% 1.41/1.04  sup_bw_superposition:                   12
% 1.41/1.04  sup_immediate_simplified:               6
% 1.41/1.04  sup_given_eliminated:                   0
% 1.41/1.04  comparisons_done:                       0
% 1.41/1.04  comparisons_avoided:                    0
% 1.41/1.04  
% 1.41/1.04  ------ Simplifications
% 1.41/1.04  
% 1.41/1.04  
% 1.41/1.04  sim_fw_subset_subsumed:                 1
% 1.41/1.04  sim_bw_subset_subsumed:                 0
% 1.41/1.04  sim_fw_subsumed:                        4
% 1.41/1.04  sim_bw_subsumed:                        0
% 1.41/1.04  sim_fw_subsumption_res:                 1
% 1.41/1.04  sim_bw_subsumption_res:                 1
% 1.41/1.04  sim_tautology_del:                      2
% 1.41/1.04  sim_eq_tautology_del:                   0
% 1.41/1.04  sim_eq_res_simp:                        0
% 1.41/1.04  sim_fw_demodulated:                     0
% 1.41/1.04  sim_bw_demodulated:                     0
% 1.41/1.04  sim_light_normalised:                   1
% 1.41/1.04  sim_joinable_taut:                      0
% 1.41/1.04  sim_joinable_simp:                      0
% 1.41/1.04  sim_ac_normalised:                      0
% 1.41/1.04  sim_smt_subsumption:                    0
% 1.41/1.04  
%------------------------------------------------------------------------------
