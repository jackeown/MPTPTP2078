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
% DateTime   : Thu Dec  3 12:12:32 EST 2020

% Result     : Theorem 1.34s
% Output     : CNFRefutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 202 expanded)
%              Number of clauses        :   48 (  57 expanded)
%              Number of leaves         :   13 (  52 expanded)
%              Depth                    :   19
%              Number of atoms          :  360 (1033 expanded)
%              Number of equality atoms :   77 ( 193 expanded)
%              Maximal formula depth    :   17 (   5 average)
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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
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

fof(f31,plain,
    ( k1_xboole_0 != k3_orders_2(sK1,k1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f30,f29])).

fof(f48,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f25])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f31])).

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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    k1_xboole_0 != k3_orders_2(sK1,k1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_580,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_581,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f41])).

cnf(c_14,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_308,plain,
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
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_309,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_13,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_313,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_17,c_16,c_15,c_13])).

cnf(c_576,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_977,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_581,c_576])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_262,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_266,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_262,c_17,c_16,c_15,c_13])).

cnf(c_578,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_582,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1011,plain,
    ( r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_582])).

cnf(c_1061,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_581,c_1011])).

cnf(c_1106,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
    | k3_orders_2(sK1,X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_977,c_1061])).

cnf(c_1107,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1106])).

cnf(c_1,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_583,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_192,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_193,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_192])).

cnf(c_579,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_874,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_583,c_579])).

cnf(c_1119,plain,
    ( k3_orders_2(sK1,k1_xboole_0,X0) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1107,c_874])).

cnf(c_746,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_751,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_1278,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | k3_orders_2(sK1,k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1119,c_751])).

cnf(c_1279,plain,
    ( k3_orders_2(sK1,k1_xboole_0,X0) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1278])).

cnf(c_1286,plain,
    ( k3_orders_2(sK1,k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_580,c_1279])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != k3_orders_2(sK1,k1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_207,plain,
    ( ~ l1_orders_2(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7,c_5])).

cnf(c_352,plain,
    ( k1_struct_0(X0) = k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_207,c_13])).

cnf(c_353,plain,
    ( k1_struct_0(sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_590,plain,
    ( k3_orders_2(sK1,k1_xboole_0,sK2) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11,c_353])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1286,c_590])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.34/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.34/0.98  
% 1.34/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.34/0.98  
% 1.34/0.98  ------  iProver source info
% 1.34/0.98  
% 1.34/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.34/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.34/0.98  git: non_committed_changes: false
% 1.34/0.98  git: last_make_outside_of_git: false
% 1.34/0.98  
% 1.34/0.98  ------ 
% 1.34/0.98  
% 1.34/0.98  ------ Input Options
% 1.34/0.98  
% 1.34/0.98  --out_options                           all
% 1.34/0.98  --tptp_safe_out                         true
% 1.34/0.98  --problem_path                          ""
% 1.34/0.98  --include_path                          ""
% 1.34/0.98  --clausifier                            res/vclausify_rel
% 1.34/0.98  --clausifier_options                    --mode clausify
% 1.34/0.98  --stdin                                 false
% 1.34/0.98  --stats_out                             all
% 1.34/0.98  
% 1.34/0.98  ------ General Options
% 1.34/0.98  
% 1.34/0.98  --fof                                   false
% 1.34/0.98  --time_out_real                         305.
% 1.34/0.98  --time_out_virtual                      -1.
% 1.34/0.98  --symbol_type_check                     false
% 1.34/0.98  --clausify_out                          false
% 1.34/0.98  --sig_cnt_out                           false
% 1.34/0.98  --trig_cnt_out                          false
% 1.34/0.98  --trig_cnt_out_tolerance                1.
% 1.34/0.98  --trig_cnt_out_sk_spl                   false
% 1.34/0.98  --abstr_cl_out                          false
% 1.34/0.98  
% 1.34/0.98  ------ Global Options
% 1.34/0.98  
% 1.34/0.98  --schedule                              default
% 1.34/0.98  --add_important_lit                     false
% 1.34/0.98  --prop_solver_per_cl                    1000
% 1.34/0.98  --min_unsat_core                        false
% 1.34/0.98  --soft_assumptions                      false
% 1.34/0.98  --soft_lemma_size                       3
% 1.34/0.98  --prop_impl_unit_size                   0
% 1.34/0.98  --prop_impl_unit                        []
% 1.34/0.98  --share_sel_clauses                     true
% 1.34/0.98  --reset_solvers                         false
% 1.34/0.98  --bc_imp_inh                            [conj_cone]
% 1.34/0.98  --conj_cone_tolerance                   3.
% 1.34/0.98  --extra_neg_conj                        none
% 1.34/0.98  --large_theory_mode                     true
% 1.34/0.98  --prolific_symb_bound                   200
% 1.34/0.98  --lt_threshold                          2000
% 1.34/0.98  --clause_weak_htbl                      true
% 1.34/0.98  --gc_record_bc_elim                     false
% 1.34/0.98  
% 1.34/0.98  ------ Preprocessing Options
% 1.34/0.98  
% 1.34/0.98  --preprocessing_flag                    true
% 1.34/0.98  --time_out_prep_mult                    0.1
% 1.34/0.98  --splitting_mode                        input
% 1.34/0.98  --splitting_grd                         true
% 1.34/0.98  --splitting_cvd                         false
% 1.34/0.98  --splitting_cvd_svl                     false
% 1.34/0.98  --splitting_nvd                         32
% 1.34/0.98  --sub_typing                            true
% 1.34/0.98  --prep_gs_sim                           true
% 1.34/0.98  --prep_unflatten                        true
% 1.34/0.98  --prep_res_sim                          true
% 1.34/0.98  --prep_upred                            true
% 1.34/0.98  --prep_sem_filter                       exhaustive
% 1.34/0.98  --prep_sem_filter_out                   false
% 1.34/0.98  --pred_elim                             true
% 1.34/0.98  --res_sim_input                         true
% 1.34/0.98  --eq_ax_congr_red                       true
% 1.34/0.98  --pure_diseq_elim                       true
% 1.34/0.98  --brand_transform                       false
% 1.34/0.98  --non_eq_to_eq                          false
% 1.34/0.98  --prep_def_merge                        true
% 1.34/0.98  --prep_def_merge_prop_impl              false
% 1.34/0.98  --prep_def_merge_mbd                    true
% 1.34/0.98  --prep_def_merge_tr_red                 false
% 1.34/0.98  --prep_def_merge_tr_cl                  false
% 1.34/0.98  --smt_preprocessing                     true
% 1.34/0.98  --smt_ac_axioms                         fast
% 1.34/0.98  --preprocessed_out                      false
% 1.34/0.98  --preprocessed_stats                    false
% 1.34/0.98  
% 1.34/0.98  ------ Abstraction refinement Options
% 1.34/0.98  
% 1.34/0.98  --abstr_ref                             []
% 1.34/0.98  --abstr_ref_prep                        false
% 1.34/0.98  --abstr_ref_until_sat                   false
% 1.34/0.98  --abstr_ref_sig_restrict                funpre
% 1.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.34/0.98  --abstr_ref_under                       []
% 1.34/0.98  
% 1.34/0.98  ------ SAT Options
% 1.34/0.98  
% 1.34/0.98  --sat_mode                              false
% 1.34/0.98  --sat_fm_restart_options                ""
% 1.34/0.98  --sat_gr_def                            false
% 1.34/0.98  --sat_epr_types                         true
% 1.34/0.98  --sat_non_cyclic_types                  false
% 1.34/0.98  --sat_finite_models                     false
% 1.34/0.98  --sat_fm_lemmas                         false
% 1.34/0.98  --sat_fm_prep                           false
% 1.34/0.98  --sat_fm_uc_incr                        true
% 1.34/0.98  --sat_out_model                         small
% 1.34/0.98  --sat_out_clauses                       false
% 1.34/0.98  
% 1.34/0.98  ------ QBF Options
% 1.34/0.98  
% 1.34/0.98  --qbf_mode                              false
% 1.34/0.98  --qbf_elim_univ                         false
% 1.34/0.98  --qbf_dom_inst                          none
% 1.34/0.98  --qbf_dom_pre_inst                      false
% 1.34/0.98  --qbf_sk_in                             false
% 1.34/0.98  --qbf_pred_elim                         true
% 1.34/0.98  --qbf_split                             512
% 1.34/0.98  
% 1.34/0.98  ------ BMC1 Options
% 1.34/0.98  
% 1.34/0.98  --bmc1_incremental                      false
% 1.34/0.98  --bmc1_axioms                           reachable_all
% 1.34/0.98  --bmc1_min_bound                        0
% 1.34/0.98  --bmc1_max_bound                        -1
% 1.34/0.98  --bmc1_max_bound_default                -1
% 1.34/0.98  --bmc1_symbol_reachability              true
% 1.34/0.98  --bmc1_property_lemmas                  false
% 1.34/0.98  --bmc1_k_induction                      false
% 1.34/0.98  --bmc1_non_equiv_states                 false
% 1.34/0.98  --bmc1_deadlock                         false
% 1.34/0.98  --bmc1_ucm                              false
% 1.34/0.98  --bmc1_add_unsat_core                   none
% 1.34/0.98  --bmc1_unsat_core_children              false
% 1.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.34/0.98  --bmc1_out_stat                         full
% 1.34/0.98  --bmc1_ground_init                      false
% 1.34/0.98  --bmc1_pre_inst_next_state              false
% 1.34/0.98  --bmc1_pre_inst_state                   false
% 1.34/0.98  --bmc1_pre_inst_reach_state             false
% 1.34/0.98  --bmc1_out_unsat_core                   false
% 1.34/0.98  --bmc1_aig_witness_out                  false
% 1.34/0.98  --bmc1_verbose                          false
% 1.34/0.98  --bmc1_dump_clauses_tptp                false
% 1.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.34/0.98  --bmc1_dump_file                        -
% 1.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.34/0.98  --bmc1_ucm_extend_mode                  1
% 1.34/0.98  --bmc1_ucm_init_mode                    2
% 1.34/0.98  --bmc1_ucm_cone_mode                    none
% 1.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.34/0.98  --bmc1_ucm_relax_model                  4
% 1.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.34/0.98  --bmc1_ucm_layered_model                none
% 1.34/0.98  --bmc1_ucm_max_lemma_size               10
% 1.34/0.98  
% 1.34/0.98  ------ AIG Options
% 1.34/0.98  
% 1.34/0.98  --aig_mode                              false
% 1.34/0.98  
% 1.34/0.98  ------ Instantiation Options
% 1.34/0.98  
% 1.34/0.98  --instantiation_flag                    true
% 1.34/0.98  --inst_sos_flag                         false
% 1.34/0.98  --inst_sos_phase                        true
% 1.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.34/0.98  --inst_lit_sel_side                     num_symb
% 1.34/0.98  --inst_solver_per_active                1400
% 1.34/0.98  --inst_solver_calls_frac                1.
% 1.34/0.98  --inst_passive_queue_type               priority_queues
% 1.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.34/0.98  --inst_passive_queues_freq              [25;2]
% 1.34/0.98  --inst_dismatching                      true
% 1.34/0.98  --inst_eager_unprocessed_to_passive     true
% 1.34/0.98  --inst_prop_sim_given                   true
% 1.34/0.98  --inst_prop_sim_new                     false
% 1.34/0.98  --inst_subs_new                         false
% 1.34/0.98  --inst_eq_res_simp                      false
% 1.34/0.98  --inst_subs_given                       false
% 1.34/0.98  --inst_orphan_elimination               true
% 1.34/0.98  --inst_learning_loop_flag               true
% 1.34/0.98  --inst_learning_start                   3000
% 1.34/0.98  --inst_learning_factor                  2
% 1.34/0.98  --inst_start_prop_sim_after_learn       3
% 1.34/0.98  --inst_sel_renew                        solver
% 1.34/0.98  --inst_lit_activity_flag                true
% 1.34/0.98  --inst_restr_to_given                   false
% 1.34/0.98  --inst_activity_threshold               500
% 1.34/0.98  --inst_out_proof                        true
% 1.34/0.98  
% 1.34/0.98  ------ Resolution Options
% 1.34/0.98  
% 1.34/0.98  --resolution_flag                       true
% 1.34/0.98  --res_lit_sel                           adaptive
% 1.34/0.98  --res_lit_sel_side                      none
% 1.34/0.98  --res_ordering                          kbo
% 1.34/0.98  --res_to_prop_solver                    active
% 1.34/0.98  --res_prop_simpl_new                    false
% 1.34/0.98  --res_prop_simpl_given                  true
% 1.34/0.98  --res_passive_queue_type                priority_queues
% 1.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.34/0.98  --res_passive_queues_freq               [15;5]
% 1.34/0.98  --res_forward_subs                      full
% 1.34/0.98  --res_backward_subs                     full
% 1.34/0.98  --res_forward_subs_resolution           true
% 1.34/0.98  --res_backward_subs_resolution          true
% 1.34/0.98  --res_orphan_elimination                true
% 1.34/0.98  --res_time_limit                        2.
% 1.34/0.98  --res_out_proof                         true
% 1.34/0.98  
% 1.34/0.98  ------ Superposition Options
% 1.34/0.98  
% 1.34/0.98  --superposition_flag                    true
% 1.34/0.98  --sup_passive_queue_type                priority_queues
% 1.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.34/0.98  --demod_completeness_check              fast
% 1.34/0.98  --demod_use_ground                      true
% 1.34/0.98  --sup_to_prop_solver                    passive
% 1.34/0.98  --sup_prop_simpl_new                    true
% 1.34/0.98  --sup_prop_simpl_given                  true
% 1.34/0.98  --sup_fun_splitting                     false
% 1.34/0.98  --sup_smt_interval                      50000
% 1.34/0.98  
% 1.34/0.98  ------ Superposition Simplification Setup
% 1.34/0.98  
% 1.34/0.98  --sup_indices_passive                   []
% 1.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.98  --sup_full_bw                           [BwDemod]
% 1.34/0.98  --sup_immed_triv                        [TrivRules]
% 1.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.98  --sup_immed_bw_main                     []
% 1.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.34/0.98  
% 1.34/0.98  ------ Combination Options
% 1.34/0.98  
% 1.34/0.98  --comb_res_mult                         3
% 1.34/0.98  --comb_sup_mult                         2
% 1.34/0.98  --comb_inst_mult                        10
% 1.34/0.98  
% 1.34/0.98  ------ Debug Options
% 1.34/0.98  
% 1.34/0.98  --dbg_backtrace                         false
% 1.34/0.98  --dbg_dump_prop_clauses                 false
% 1.34/0.98  --dbg_dump_prop_clauses_file            -
% 1.34/0.98  --dbg_out_stat                          false
% 1.34/0.98  ------ Parsing...
% 1.34/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.34/0.98  
% 1.34/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.34/0.98  
% 1.34/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.34/0.98  
% 1.34/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.34/0.98  ------ Proving...
% 1.34/0.98  ------ Problem Properties 
% 1.34/0.98  
% 1.34/0.98  
% 1.34/0.98  clauses                                 10
% 1.34/0.98  conjectures                             2
% 1.34/0.98  EPR                                     0
% 1.34/0.98  Horn                                    9
% 1.34/0.98  unary                                   4
% 1.34/0.98  binary                                  2
% 1.34/0.98  lits                                    25
% 1.34/0.98  lits eq                                 3
% 1.34/0.98  fd_pure                                 0
% 1.34/0.98  fd_pseudo                               0
% 1.34/0.98  fd_cond                                 1
% 1.34/0.98  fd_pseudo_cond                          0
% 1.34/0.98  AC symbols                              0
% 1.34/0.98  
% 1.34/0.98  ------ Schedule dynamic 5 is on 
% 1.34/0.98  
% 1.34/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.34/0.98  
% 1.34/0.98  
% 1.34/0.98  ------ 
% 1.34/0.98  Current options:
% 1.34/0.98  ------ 
% 1.34/0.98  
% 1.34/0.98  ------ Input Options
% 1.34/0.98  
% 1.34/0.98  --out_options                           all
% 1.34/0.98  --tptp_safe_out                         true
% 1.34/0.98  --problem_path                          ""
% 1.34/0.98  --include_path                          ""
% 1.34/0.98  --clausifier                            res/vclausify_rel
% 1.34/0.98  --clausifier_options                    --mode clausify
% 1.34/0.98  --stdin                                 false
% 1.34/0.98  --stats_out                             all
% 1.34/0.98  
% 1.34/0.98  ------ General Options
% 1.34/0.98  
% 1.34/0.98  --fof                                   false
% 1.34/0.98  --time_out_real                         305.
% 1.34/0.98  --time_out_virtual                      -1.
% 1.34/0.98  --symbol_type_check                     false
% 1.34/0.98  --clausify_out                          false
% 1.34/0.98  --sig_cnt_out                           false
% 1.34/0.98  --trig_cnt_out                          false
% 1.34/0.98  --trig_cnt_out_tolerance                1.
% 1.34/0.98  --trig_cnt_out_sk_spl                   false
% 1.34/0.98  --abstr_cl_out                          false
% 1.34/0.98  
% 1.34/0.98  ------ Global Options
% 1.34/0.98  
% 1.34/0.98  --schedule                              default
% 1.34/0.98  --add_important_lit                     false
% 1.34/0.98  --prop_solver_per_cl                    1000
% 1.34/0.98  --min_unsat_core                        false
% 1.34/0.98  --soft_assumptions                      false
% 1.34/0.98  --soft_lemma_size                       3
% 1.34/0.98  --prop_impl_unit_size                   0
% 1.34/0.98  --prop_impl_unit                        []
% 1.34/0.98  --share_sel_clauses                     true
% 1.34/0.98  --reset_solvers                         false
% 1.34/0.98  --bc_imp_inh                            [conj_cone]
% 1.34/0.98  --conj_cone_tolerance                   3.
% 1.34/0.98  --extra_neg_conj                        none
% 1.34/0.98  --large_theory_mode                     true
% 1.34/0.98  --prolific_symb_bound                   200
% 1.34/0.98  --lt_threshold                          2000
% 1.34/0.98  --clause_weak_htbl                      true
% 1.34/0.98  --gc_record_bc_elim                     false
% 1.34/0.98  
% 1.34/0.98  ------ Preprocessing Options
% 1.34/0.98  
% 1.34/0.98  --preprocessing_flag                    true
% 1.34/0.98  --time_out_prep_mult                    0.1
% 1.34/0.98  --splitting_mode                        input
% 1.34/0.98  --splitting_grd                         true
% 1.34/0.98  --splitting_cvd                         false
% 1.34/0.98  --splitting_cvd_svl                     false
% 1.34/0.98  --splitting_nvd                         32
% 1.34/0.98  --sub_typing                            true
% 1.34/0.98  --prep_gs_sim                           true
% 1.34/0.98  --prep_unflatten                        true
% 1.34/0.98  --prep_res_sim                          true
% 1.34/0.98  --prep_upred                            true
% 1.34/0.98  --prep_sem_filter                       exhaustive
% 1.34/0.98  --prep_sem_filter_out                   false
% 1.34/0.98  --pred_elim                             true
% 1.34/0.98  --res_sim_input                         true
% 1.34/0.98  --eq_ax_congr_red                       true
% 1.34/0.98  --pure_diseq_elim                       true
% 1.34/0.98  --brand_transform                       false
% 1.34/0.98  --non_eq_to_eq                          false
% 1.34/0.98  --prep_def_merge                        true
% 1.34/0.98  --prep_def_merge_prop_impl              false
% 1.34/0.98  --prep_def_merge_mbd                    true
% 1.34/0.98  --prep_def_merge_tr_red                 false
% 1.34/0.98  --prep_def_merge_tr_cl                  false
% 1.34/0.98  --smt_preprocessing                     true
% 1.34/0.98  --smt_ac_axioms                         fast
% 1.34/0.98  --preprocessed_out                      false
% 1.34/0.98  --preprocessed_stats                    false
% 1.34/0.98  
% 1.34/0.98  ------ Abstraction refinement Options
% 1.34/0.98  
% 1.34/0.98  --abstr_ref                             []
% 1.34/0.98  --abstr_ref_prep                        false
% 1.34/0.98  --abstr_ref_until_sat                   false
% 1.34/0.98  --abstr_ref_sig_restrict                funpre
% 1.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.34/0.98  --abstr_ref_under                       []
% 1.34/0.98  
% 1.34/0.98  ------ SAT Options
% 1.34/0.98  
% 1.34/0.98  --sat_mode                              false
% 1.34/0.98  --sat_fm_restart_options                ""
% 1.34/0.98  --sat_gr_def                            false
% 1.34/0.98  --sat_epr_types                         true
% 1.34/0.98  --sat_non_cyclic_types                  false
% 1.34/0.98  --sat_finite_models                     false
% 1.34/0.98  --sat_fm_lemmas                         false
% 1.34/0.98  --sat_fm_prep                           false
% 1.34/0.98  --sat_fm_uc_incr                        true
% 1.34/0.98  --sat_out_model                         small
% 1.34/0.98  --sat_out_clauses                       false
% 1.34/0.98  
% 1.34/0.98  ------ QBF Options
% 1.34/0.98  
% 1.34/0.98  --qbf_mode                              false
% 1.34/0.98  --qbf_elim_univ                         false
% 1.34/0.98  --qbf_dom_inst                          none
% 1.34/0.98  --qbf_dom_pre_inst                      false
% 1.34/0.98  --qbf_sk_in                             false
% 1.34/0.98  --qbf_pred_elim                         true
% 1.34/0.98  --qbf_split                             512
% 1.34/0.98  
% 1.34/0.98  ------ BMC1 Options
% 1.34/0.98  
% 1.34/0.98  --bmc1_incremental                      false
% 1.34/0.98  --bmc1_axioms                           reachable_all
% 1.34/0.98  --bmc1_min_bound                        0
% 1.34/0.98  --bmc1_max_bound                        -1
% 1.34/0.98  --bmc1_max_bound_default                -1
% 1.34/0.98  --bmc1_symbol_reachability              true
% 1.34/0.98  --bmc1_property_lemmas                  false
% 1.34/0.98  --bmc1_k_induction                      false
% 1.34/0.98  --bmc1_non_equiv_states                 false
% 1.34/0.98  --bmc1_deadlock                         false
% 1.34/0.98  --bmc1_ucm                              false
% 1.34/0.98  --bmc1_add_unsat_core                   none
% 1.34/0.98  --bmc1_unsat_core_children              false
% 1.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.34/0.98  --bmc1_out_stat                         full
% 1.34/0.98  --bmc1_ground_init                      false
% 1.34/0.98  --bmc1_pre_inst_next_state              false
% 1.34/0.98  --bmc1_pre_inst_state                   false
% 1.34/0.98  --bmc1_pre_inst_reach_state             false
% 1.34/0.98  --bmc1_out_unsat_core                   false
% 1.34/0.98  --bmc1_aig_witness_out                  false
% 1.34/0.98  --bmc1_verbose                          false
% 1.34/0.98  --bmc1_dump_clauses_tptp                false
% 1.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.34/0.98  --bmc1_dump_file                        -
% 1.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.34/0.98  --bmc1_ucm_extend_mode                  1
% 1.34/0.98  --bmc1_ucm_init_mode                    2
% 1.34/0.98  --bmc1_ucm_cone_mode                    none
% 1.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.34/0.98  --bmc1_ucm_relax_model                  4
% 1.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.34/0.98  --bmc1_ucm_layered_model                none
% 1.34/0.98  --bmc1_ucm_max_lemma_size               10
% 1.34/0.98  
% 1.34/0.98  ------ AIG Options
% 1.34/0.98  
% 1.34/0.98  --aig_mode                              false
% 1.34/0.98  
% 1.34/0.98  ------ Instantiation Options
% 1.34/0.98  
% 1.34/0.98  --instantiation_flag                    true
% 1.34/0.98  --inst_sos_flag                         false
% 1.34/0.98  --inst_sos_phase                        true
% 1.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.34/0.98  --inst_lit_sel_side                     none
% 1.34/0.98  --inst_solver_per_active                1400
% 1.34/0.98  --inst_solver_calls_frac                1.
% 1.34/0.98  --inst_passive_queue_type               priority_queues
% 1.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.34/0.98  --inst_passive_queues_freq              [25;2]
% 1.34/0.98  --inst_dismatching                      true
% 1.34/0.98  --inst_eager_unprocessed_to_passive     true
% 1.34/0.98  --inst_prop_sim_given                   true
% 1.34/0.98  --inst_prop_sim_new                     false
% 1.34/0.98  --inst_subs_new                         false
% 1.34/0.98  --inst_eq_res_simp                      false
% 1.34/0.98  --inst_subs_given                       false
% 1.34/0.98  --inst_orphan_elimination               true
% 1.34/0.98  --inst_learning_loop_flag               true
% 1.34/0.98  --inst_learning_start                   3000
% 1.34/0.98  --inst_learning_factor                  2
% 1.34/0.98  --inst_start_prop_sim_after_learn       3
% 1.34/0.98  --inst_sel_renew                        solver
% 1.34/0.98  --inst_lit_activity_flag                true
% 1.34/0.98  --inst_restr_to_given                   false
% 1.34/0.98  --inst_activity_threshold               500
% 1.34/0.98  --inst_out_proof                        true
% 1.34/0.98  
% 1.34/0.98  ------ Resolution Options
% 1.34/0.98  
% 1.34/0.98  --resolution_flag                       false
% 1.34/0.98  --res_lit_sel                           adaptive
% 1.34/0.98  --res_lit_sel_side                      none
% 1.34/0.98  --res_ordering                          kbo
% 1.34/0.98  --res_to_prop_solver                    active
% 1.34/0.98  --res_prop_simpl_new                    false
% 1.34/0.98  --res_prop_simpl_given                  true
% 1.34/0.98  --res_passive_queue_type                priority_queues
% 1.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.34/0.98  --res_passive_queues_freq               [15;5]
% 1.34/0.98  --res_forward_subs                      full
% 1.34/0.98  --res_backward_subs                     full
% 1.34/0.98  --res_forward_subs_resolution           true
% 1.34/0.98  --res_backward_subs_resolution          true
% 1.34/0.98  --res_orphan_elimination                true
% 1.34/0.98  --res_time_limit                        2.
% 1.34/0.98  --res_out_proof                         true
% 1.34/0.98  
% 1.34/0.98  ------ Superposition Options
% 1.34/0.98  
% 1.34/0.98  --superposition_flag                    true
% 1.34/0.98  --sup_passive_queue_type                priority_queues
% 1.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.34/0.98  --demod_completeness_check              fast
% 1.34/0.98  --demod_use_ground                      true
% 1.34/0.98  --sup_to_prop_solver                    passive
% 1.34/0.98  --sup_prop_simpl_new                    true
% 1.34/0.98  --sup_prop_simpl_given                  true
% 1.34/0.98  --sup_fun_splitting                     false
% 1.34/0.98  --sup_smt_interval                      50000
% 1.34/0.98  
% 1.34/0.98  ------ Superposition Simplification Setup
% 1.34/0.98  
% 1.34/0.98  --sup_indices_passive                   []
% 1.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.98  --sup_full_bw                           [BwDemod]
% 1.34/0.98  --sup_immed_triv                        [TrivRules]
% 1.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.98  --sup_immed_bw_main                     []
% 1.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.34/0.98  
% 1.34/0.98  ------ Combination Options
% 1.34/0.98  
% 1.34/0.98  --comb_res_mult                         3
% 1.34/0.98  --comb_sup_mult                         2
% 1.34/0.98  --comb_inst_mult                        10
% 1.34/0.98  
% 1.34/0.98  ------ Debug Options
% 1.34/0.98  
% 1.34/0.98  --dbg_backtrace                         false
% 1.34/0.98  --dbg_dump_prop_clauses                 false
% 1.34/0.98  --dbg_dump_prop_clauses_file            -
% 1.34/0.98  --dbg_out_stat                          false
% 1.34/0.98  
% 1.34/0.98  
% 1.34/0.98  
% 1.34/0.98  
% 1.34/0.98  ------ Proving...
% 1.34/0.98  
% 1.34/0.98  
% 1.34/0.98  % SZS status Theorem for theBenchmark.p
% 1.34/0.98  
% 1.34/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.34/0.98  
% 1.34/0.98  fof(f10,conjecture,(
% 1.34/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 1.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.34/0.98  
% 1.34/0.98  fof(f11,negated_conjecture,(
% 1.34/0.98    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 1.34/0.98    inference(negated_conjecture,[],[f10])).
% 1.34/0.98  
% 1.34/0.98  fof(f23,plain,(
% 1.34/0.98    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.34/0.98    inference(ennf_transformation,[],[f11])).
% 1.34/0.98  
% 1.34/0.98  fof(f24,plain,(
% 1.34/0.98    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.34/0.98    inference(flattening,[],[f23])).
% 1.34/0.98  
% 1.34/0.98  fof(f30,plain,(
% 1.34/0.98    ( ! [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) => (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),sK2) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.34/0.98    introduced(choice_axiom,[])).
% 1.34/0.98  
% 1.34/0.98  fof(f29,plain,(
% 1.34/0.98    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 != k3_orders_2(sK1,k1_struct_0(sK1),X1) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.34/0.98    introduced(choice_axiom,[])).
% 1.34/0.98  
% 1.34/0.98  fof(f31,plain,(
% 1.34/0.98    (k1_xboole_0 != k3_orders_2(sK1,k1_struct_0(sK1),sK2) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 1.34/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f30,f29])).
% 1.34/0.98  
% 1.34/0.98  fof(f48,plain,(
% 1.34/0.98    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.34/0.98    inference(cnf_transformation,[],[f31])).
% 1.34/0.98  
% 1.34/0.98  fof(f5,axiom,(
% 1.34/0.98    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.34/0.98  
% 1.34/0.98  fof(f12,plain,(
% 1.34/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.34/0.98    inference(pure_predicate_removal,[],[f5])).
% 1.34/0.98  
% 1.34/0.98  fof(f16,plain,(
% 1.34/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.34/0.98    inference(ennf_transformation,[],[f12])).
% 1.34/0.98  
% 1.34/0.98  fof(f25,plain,(
% 1.34/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.34/0.98    introduced(choice_axiom,[])).
% 1.34/0.98  
% 1.34/0.98  fof(f26,plain,(
% 1.34/0.98    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 1.34/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f25])).
% 1.34/0.98  
% 1.34/0.98  fof(f36,plain,(
% 1.34/0.98    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.34/0.98    inference(cnf_transformation,[],[f26])).
% 1.34/0.98  
% 1.34/0.98  fof(f9,axiom,(
% 1.34/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 1.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.34/0.98  
% 1.34/0.98  fof(f21,plain,(
% 1.34/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.34/0.98    inference(ennf_transformation,[],[f9])).
% 1.34/0.98  
% 1.34/0.98  fof(f22,plain,(
% 1.34/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.34/0.98    inference(flattening,[],[f21])).
% 1.34/0.98  
% 1.34/0.98  fof(f27,plain,(
% 1.34/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.34/0.98    inference(nnf_transformation,[],[f22])).
% 1.34/0.98  
% 1.34/0.98  fof(f28,plain,(
% 1.34/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.34/0.98    inference(flattening,[],[f27])).
% 1.34/0.98  
% 1.34/0.98  fof(f41,plain,(
% 1.34/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.34/0.98    inference(cnf_transformation,[],[f28])).
% 1.34/0.98  
% 1.34/0.98  fof(f46,plain,(
% 1.34/0.98    v5_orders_2(sK1)),
% 1.34/0.98    inference(cnf_transformation,[],[f31])).
% 1.34/0.98  
% 1.34/0.98  fof(f43,plain,(
% 1.34/0.98    ~v2_struct_0(sK1)),
% 1.34/0.98    inference(cnf_transformation,[],[f31])).
% 1.34/0.98  
% 1.34/0.98  fof(f44,plain,(
% 1.34/0.98    v3_orders_2(sK1)),
% 1.34/0.98    inference(cnf_transformation,[],[f31])).
% 1.34/0.98  
% 1.34/0.98  fof(f45,plain,(
% 1.34/0.98    v4_orders_2(sK1)),
% 1.34/0.98    inference(cnf_transformation,[],[f31])).
% 1.34/0.98  
% 1.34/0.98  fof(f47,plain,(
% 1.34/0.98    l1_orders_2(sK1)),
% 1.34/0.98    inference(cnf_transformation,[],[f31])).
% 1.34/0.98  
% 1.34/0.98  fof(f7,axiom,(
% 1.34/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.34/0.98  
% 1.34/0.98  fof(f18,plain,(
% 1.34/0.98    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.34/0.98    inference(ennf_transformation,[],[f7])).
% 1.34/0.98  
% 1.34/0.98  fof(f19,plain,(
% 1.34/0.98    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.34/0.98    inference(flattening,[],[f18])).
% 1.34/0.98  
% 1.34/0.98  fof(f38,plain,(
% 1.34/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.34/0.98    inference(cnf_transformation,[],[f19])).
% 1.34/0.98  
% 1.34/0.98  fof(f3,axiom,(
% 1.34/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.34/0.98  
% 1.34/0.98  fof(f13,plain,(
% 1.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.34/0.98    inference(ennf_transformation,[],[f3])).
% 1.34/0.98  
% 1.34/0.98  fof(f14,plain,(
% 1.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.34/0.98    inference(flattening,[],[f13])).
% 1.34/0.98  
% 1.34/0.98  fof(f34,plain,(
% 1.34/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.34/0.98    inference(cnf_transformation,[],[f14])).
% 1.34/0.98  
% 1.34/0.98  fof(f2,axiom,(
% 1.34/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.34/0.98  
% 1.34/0.98  fof(f33,plain,(
% 1.34/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.34/0.98    inference(cnf_transformation,[],[f2])).
% 1.34/0.98  
% 1.34/0.98  fof(f1,axiom,(
% 1.34/0.98    v1_xboole_0(k1_xboole_0)),
% 1.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.34/0.98  
% 1.34/0.98  fof(f32,plain,(
% 1.34/0.98    v1_xboole_0(k1_xboole_0)),
% 1.34/0.98    inference(cnf_transformation,[],[f1])).
% 1.34/0.98  
% 1.34/0.98  fof(f4,axiom,(
% 1.34/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.34/0.98  
% 1.34/0.98  fof(f15,plain,(
% 1.34/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.34/0.98    inference(ennf_transformation,[],[f4])).
% 1.34/0.98  
% 1.34/0.98  fof(f35,plain,(
% 1.34/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.34/0.98    inference(cnf_transformation,[],[f15])).
% 1.34/0.98  
% 1.34/0.98  fof(f49,plain,(
% 1.34/0.98    k1_xboole_0 != k3_orders_2(sK1,k1_struct_0(sK1),sK2)),
% 1.34/0.98    inference(cnf_transformation,[],[f31])).
% 1.34/0.98  
% 1.34/0.98  fof(f8,axiom,(
% 1.34/0.98    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.34/0.98  
% 1.34/0.98  fof(f20,plain,(
% 1.34/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.34/0.98    inference(ennf_transformation,[],[f8])).
% 1.34/0.98  
% 1.34/0.98  fof(f39,plain,(
% 1.34/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.34/0.98    inference(cnf_transformation,[],[f20])).
% 1.34/0.98  
% 1.34/0.98  fof(f6,axiom,(
% 1.34/0.98    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 1.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.34/0.98  
% 1.34/0.98  fof(f17,plain,(
% 1.34/0.98    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.34/0.98    inference(ennf_transformation,[],[f6])).
% 1.34/0.98  
% 1.34/0.98  fof(f37,plain,(
% 1.34/0.98    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.34/0.98    inference(cnf_transformation,[],[f17])).
% 1.34/0.98  
% 1.34/0.98  cnf(c_12,negated_conjecture,
% 1.34/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.34/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.34/0.98  
% 1.34/0.98  cnf(c_580,plain,
% 1.34/0.98      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.34/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.34/0.98  
% 1.34/0.98  cnf(c_4,plain,
% 1.34/0.98      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.34/0.98      inference(cnf_transformation,[],[f36]) ).
% 1.34/0.98  
% 1.34/0.98  cnf(c_581,plain,
% 1.34/0.98      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 1.34/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.34/0.98  
% 1.34/0.98  cnf(c_9,plain,
% 1.34/0.98      ( r2_hidden(X0,X1)
% 1.34/0.98      | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
% 1.34/0.98      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.34/0.98      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 1.34/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.34/0.98      | v2_struct_0(X2)
% 1.34/0.98      | ~ v3_orders_2(X2)
% 1.34/0.98      | ~ v4_orders_2(X2)
% 1.34/0.98      | ~ v5_orders_2(X2)
% 1.34/0.98      | ~ l1_orders_2(X2) ),
% 1.34/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.34/0.98  
% 1.34/0.98  cnf(c_14,negated_conjecture,
% 1.34/0.98      ( v5_orders_2(sK1) ),
% 1.34/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.34/0.98  
% 1.34/0.98  cnf(c_308,plain,
% 1.34/0.98      ( r2_hidden(X0,X1)
% 1.34/0.98      | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
% 1.34/0.98      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.34/0.98      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 1.34/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.34/0.98      | v2_struct_0(X2)
% 1.34/0.98      | ~ v3_orders_2(X2)
% 1.34/0.98      | ~ v4_orders_2(X2)
% 1.34/0.98      | ~ l1_orders_2(X2)
% 1.34/0.98      | sK1 != X2 ),
% 1.34/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 1.34/0.98  
% 1.34/0.98  cnf(c_309,plain,
% 1.34/0.98      ( r2_hidden(X0,X1)
% 1.34/0.98      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
% 1.34/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.34/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.34/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.34/0.98      | v2_struct_0(sK1)
% 1.34/0.98      | ~ v3_orders_2(sK1)
% 1.34/0.98      | ~ v4_orders_2(sK1)
% 1.34/0.98      | ~ l1_orders_2(sK1) ),
% 1.34/0.98      inference(unflattening,[status(thm)],[c_308]) ).
% 1.34/0.98  
% 1.34/0.98  cnf(c_17,negated_conjecture,
% 1.34/0.98      ( ~ v2_struct_0(sK1) ),
% 1.34/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.34/0.98  
% 1.34/0.98  cnf(c_16,negated_conjecture,
% 1.34/0.98      ( v3_orders_2(sK1) ),
% 1.34/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.34/0.98  
% 1.34/0.98  cnf(c_15,negated_conjecture,
% 1.34/0.98      ( v4_orders_2(sK1) ),
% 1.34/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.34/0.98  
% 1.34/0.98  cnf(c_13,negated_conjecture,
% 1.34/0.98      ( l1_orders_2(sK1) ),
% 1.34/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.34/0.98  
% 1.34/0.98  cnf(c_313,plain,
% 1.34/0.98      ( r2_hidden(X0,X1)
% 1.34/0.98      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
% 1.34/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.34/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.34/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.34/0.98      inference(global_propositional_subsumption,
% 1.34/0.98                [status(thm)],
% 1.34/0.98                [c_309,c_17,c_16,c_15,c_13]) ).
% 1.34/0.98  
% 1.34/0.98  cnf(c_576,plain,
% 1.34/0.98      ( r2_hidden(X0,X1) = iProver_top
% 1.34/0.98      | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
% 1.34/0.98      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 1.34/0.98      | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
% 1.34/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.34/0.98      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 1.34/0.98  
% 1.34/0.98  cnf(c_977,plain,
% 1.34/0.98      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 1.34/0.98      | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
% 1.34/0.98      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 1.34/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.34/0.98      | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) != iProver_top ),
% 1.34/0.98      inference(superposition,[status(thm)],[c_581,c_576]) ).
% 1.34/0.98  
% 1.34/0.98  cnf(c_6,plain,
% 1.34/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.34/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.34/0.98      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.34/0.98      | v2_struct_0(X1)
% 1.34/0.98      | ~ v3_orders_2(X1)
% 1.34/0.99      | ~ v4_orders_2(X1)
% 1.34/0.99      | ~ v5_orders_2(X1)
% 1.34/0.99      | ~ l1_orders_2(X1) ),
% 1.34/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_261,plain,
% 1.34/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.34/0.99      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.34/0.99      | v2_struct_0(X1)
% 1.34/0.99      | ~ v3_orders_2(X1)
% 1.34/0.99      | ~ v4_orders_2(X1)
% 1.34/0.99      | ~ l1_orders_2(X1)
% 1.34/0.99      | sK1 != X1 ),
% 1.34/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_14]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_262,plain,
% 1.34/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.34/0.99      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.34/0.99      | v2_struct_0(sK1)
% 1.34/0.99      | ~ v3_orders_2(sK1)
% 1.34/0.99      | ~ v4_orders_2(sK1)
% 1.34/0.99      | ~ l1_orders_2(sK1) ),
% 1.34/0.99      inference(unflattening,[status(thm)],[c_261]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_266,plain,
% 1.34/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.34/0.99      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.34/0.99      inference(global_propositional_subsumption,
% 1.34/0.99                [status(thm)],
% 1.34/0.99                [c_262,c_17,c_16,c_15,c_13]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_578,plain,
% 1.34/0.99      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 1.34/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.34/0.99      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.34/0.99      inference(predicate_to_equality,[status(thm)],[c_266]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_2,plain,
% 1.34/0.99      ( ~ r2_hidden(X0,X1)
% 1.34/0.99      | m1_subset_1(X0,X2)
% 1.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 1.34/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_582,plain,
% 1.34/0.99      ( r2_hidden(X0,X1) != iProver_top
% 1.34/0.99      | m1_subset_1(X0,X2) = iProver_top
% 1.34/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 1.34/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_1011,plain,
% 1.34/0.99      ( r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
% 1.34/0.99      | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
% 1.34/0.99      | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
% 1.34/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.34/0.99      inference(superposition,[status(thm)],[c_578,c_582]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_1061,plain,
% 1.34/0.99      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 1.34/0.99      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 1.34/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.34/0.99      | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) = iProver_top ),
% 1.34/0.99      inference(superposition,[status(thm)],[c_581,c_1011]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_1106,plain,
% 1.34/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.34/0.99      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 1.34/0.99      | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
% 1.34/0.99      | k3_orders_2(sK1,X0,X1) = k1_xboole_0 ),
% 1.34/0.99      inference(global_propositional_subsumption,
% 1.34/0.99                [status(thm)],
% 1.34/0.99                [c_977,c_1061]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_1107,plain,
% 1.34/0.99      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 1.34/0.99      | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
% 1.34/0.99      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 1.34/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.34/0.99      inference(renaming,[status(thm)],[c_1106]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_1,plain,
% 1.34/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.34/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_583,plain,
% 1.34/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.34/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_0,plain,
% 1.34/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 1.34/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_3,plain,
% 1.34/0.99      ( ~ r2_hidden(X0,X1)
% 1.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.34/0.99      | ~ v1_xboole_0(X2) ),
% 1.34/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_192,plain,
% 1.34/0.99      ( ~ r2_hidden(X0,X1)
% 1.34/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.34/0.99      | k1_xboole_0 != X2 ),
% 1.34/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_193,plain,
% 1.34/0.99      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
% 1.34/0.99      inference(unflattening,[status(thm)],[c_192]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_579,plain,
% 1.34/0.99      ( r2_hidden(X0,X1) != iProver_top
% 1.34/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.34/0.99      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_874,plain,
% 1.34/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.34/0.99      inference(superposition,[status(thm)],[c_583,c_579]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_1119,plain,
% 1.34/0.99      ( k3_orders_2(sK1,k1_xboole_0,X0) = k1_xboole_0
% 1.34/0.99      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 1.34/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.34/0.99      inference(superposition,[status(thm)],[c_1107,c_874]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_746,plain,
% 1.34/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.34/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_751,plain,
% 1.34/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.34/0.99      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_1278,plain,
% 1.34/0.99      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 1.34/0.99      | k3_orders_2(sK1,k1_xboole_0,X0) = k1_xboole_0 ),
% 1.34/0.99      inference(global_propositional_subsumption,
% 1.34/0.99                [status(thm)],
% 1.34/0.99                [c_1119,c_751]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_1279,plain,
% 1.34/0.99      ( k3_orders_2(sK1,k1_xboole_0,X0) = k1_xboole_0
% 1.34/0.99      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 1.34/0.99      inference(renaming,[status(thm)],[c_1278]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_1286,plain,
% 1.34/0.99      ( k3_orders_2(sK1,k1_xboole_0,sK2) = k1_xboole_0 ),
% 1.34/0.99      inference(superposition,[status(thm)],[c_580,c_1279]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_11,negated_conjecture,
% 1.34/0.99      ( k1_xboole_0 != k3_orders_2(sK1,k1_struct_0(sK1),sK2) ),
% 1.34/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_7,plain,
% 1.34/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.34/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_5,plain,
% 1.34/0.99      ( ~ l1_struct_0(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 1.34/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_207,plain,
% 1.34/0.99      ( ~ l1_orders_2(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 1.34/0.99      inference(resolution,[status(thm)],[c_7,c_5]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_352,plain,
% 1.34/0.99      ( k1_struct_0(X0) = k1_xboole_0 | sK1 != X0 ),
% 1.34/0.99      inference(resolution_lifted,[status(thm)],[c_207,c_13]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_353,plain,
% 1.34/0.99      ( k1_struct_0(sK1) = k1_xboole_0 ),
% 1.34/0.99      inference(unflattening,[status(thm)],[c_352]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(c_590,plain,
% 1.34/0.99      ( k3_orders_2(sK1,k1_xboole_0,sK2) != k1_xboole_0 ),
% 1.34/0.99      inference(light_normalisation,[status(thm)],[c_11,c_353]) ).
% 1.34/0.99  
% 1.34/0.99  cnf(contradiction,plain,
% 1.34/0.99      ( $false ),
% 1.34/0.99      inference(minisat,[status(thm)],[c_1286,c_590]) ).
% 1.34/0.99  
% 1.34/0.99  
% 1.34/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.34/0.99  
% 1.34/0.99  ------                               Statistics
% 1.34/0.99  
% 1.34/0.99  ------ General
% 1.34/0.99  
% 1.34/0.99  abstr_ref_over_cycles:                  0
% 1.34/0.99  abstr_ref_under_cycles:                 0
% 1.34/0.99  gc_basic_clause_elim:                   0
% 1.34/0.99  forced_gc_time:                         0
% 1.34/0.99  parsing_time:                           0.009
% 1.34/0.99  unif_index_cands_time:                  0.
% 1.34/0.99  unif_index_add_time:                    0.
% 1.34/0.99  orderings_time:                         0.
% 1.34/0.99  out_proof_time:                         0.012
% 1.34/0.99  total_time:                             0.082
% 1.34/0.99  num_of_symbols:                         46
% 1.34/0.99  num_of_terms:                           1156
% 1.34/0.99  
% 1.34/0.99  ------ Preprocessing
% 1.34/0.99  
% 1.34/0.99  num_of_splits:                          0
% 1.34/0.99  num_of_split_atoms:                     0
% 1.34/0.99  num_of_reused_defs:                     0
% 1.34/0.99  num_eq_ax_congr_red:                    7
% 1.34/0.99  num_of_sem_filtered_clauses:            1
% 1.34/0.99  num_of_subtypes:                        0
% 1.34/0.99  monotx_restored_types:                  0
% 1.34/0.99  sat_num_of_epr_types:                   0
% 1.34/0.99  sat_num_of_non_cyclic_types:            0
% 1.34/0.99  sat_guarded_non_collapsed_types:        0
% 1.34/0.99  num_pure_diseq_elim:                    0
% 1.34/0.99  simp_replaced_by:                       0
% 1.34/0.99  res_preprocessed:                       65
% 1.34/0.99  prep_upred:                             0
% 1.34/0.99  prep_unflattend:                        5
% 1.34/0.99  smt_new_axioms:                         0
% 1.34/0.99  pred_elim_cands:                        2
% 1.34/0.99  pred_elim:                              8
% 1.34/0.99  pred_elim_cl:                           8
% 1.34/0.99  pred_elim_cycles:                       10
% 1.34/0.99  merged_defs:                            0
% 1.34/0.99  merged_defs_ncl:                        0
% 1.34/0.99  bin_hyper_res:                          0
% 1.34/0.99  prep_cycles:                            4
% 1.34/0.99  pred_elim_time:                         0.005
% 1.34/0.99  splitting_time:                         0.
% 1.34/0.99  sem_filter_time:                        0.
% 1.34/0.99  monotx_time:                            0.001
% 1.34/0.99  subtype_inf_time:                       0.
% 1.34/0.99  
% 1.34/0.99  ------ Problem properties
% 1.34/0.99  
% 1.34/0.99  clauses:                                10
% 1.34/0.99  conjectures:                            2
% 1.34/0.99  epr:                                    0
% 1.34/0.99  horn:                                   9
% 1.34/0.99  ground:                                 3
% 1.34/0.99  unary:                                  4
% 1.34/0.99  binary:                                 2
% 1.34/0.99  lits:                                   25
% 1.34/0.99  lits_eq:                                3
% 1.34/0.99  fd_pure:                                0
% 1.34/0.99  fd_pseudo:                              0
% 1.34/0.99  fd_cond:                                1
% 1.34/0.99  fd_pseudo_cond:                         0
% 1.34/0.99  ac_symbols:                             0
% 1.34/0.99  
% 1.34/0.99  ------ Propositional Solver
% 1.34/0.99  
% 1.34/0.99  prop_solver_calls:                      25
% 1.34/0.99  prop_fast_solver_calls:                 482
% 1.34/0.99  smt_solver_calls:                       0
% 1.34/0.99  smt_fast_solver_calls:                  0
% 1.34/0.99  prop_num_of_clauses:                    402
% 1.34/0.99  prop_preprocess_simplified:             1919
% 1.34/0.99  prop_fo_subsumed:                       14
% 1.34/0.99  prop_solver_time:                       0.
% 1.34/0.99  smt_solver_time:                        0.
% 1.34/0.99  smt_fast_solver_time:                   0.
% 1.34/0.99  prop_fast_solver_time:                  0.
% 1.34/0.99  prop_unsat_core_time:                   0.
% 1.34/0.99  
% 1.34/0.99  ------ QBF
% 1.34/0.99  
% 1.34/0.99  qbf_q_res:                              0
% 1.34/0.99  qbf_num_tautologies:                    0
% 1.34/0.99  qbf_prep_cycles:                        0
% 1.34/0.99  
% 1.34/0.99  ------ BMC1
% 1.34/0.99  
% 1.34/0.99  bmc1_current_bound:                     -1
% 1.34/0.99  bmc1_last_solved_bound:                 -1
% 1.34/0.99  bmc1_unsat_core_size:                   -1
% 1.34/0.99  bmc1_unsat_core_parents_size:           -1
% 1.34/0.99  bmc1_merge_next_fun:                    0
% 1.34/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.34/0.99  
% 1.34/0.99  ------ Instantiation
% 1.34/0.99  
% 1.34/0.99  inst_num_of_clauses:                    116
% 1.34/0.99  inst_num_in_passive:                    5
% 1.34/0.99  inst_num_in_active:                     73
% 1.34/0.99  inst_num_in_unprocessed:                38
% 1.34/0.99  inst_num_of_loops:                      80
% 1.34/0.99  inst_num_of_learning_restarts:          0
% 1.34/0.99  inst_num_moves_active_passive:          5
% 1.34/0.99  inst_lit_activity:                      0
% 1.34/0.99  inst_lit_activity_moves:                0
% 1.34/0.99  inst_num_tautologies:                   0
% 1.34/0.99  inst_num_prop_implied:                  0
% 1.34/0.99  inst_num_existing_simplified:           0
% 1.34/0.99  inst_num_eq_res_simplified:             0
% 1.34/0.99  inst_num_child_elim:                    0
% 1.34/0.99  inst_num_of_dismatching_blockings:      12
% 1.34/0.99  inst_num_of_non_proper_insts:           77
% 1.34/0.99  inst_num_of_duplicates:                 0
% 1.34/0.99  inst_inst_num_from_inst_to_res:         0
% 1.34/0.99  inst_dismatching_checking_time:         0.
% 1.34/0.99  
% 1.34/0.99  ------ Resolution
% 1.34/0.99  
% 1.34/0.99  res_num_of_clauses:                     0
% 1.34/0.99  res_num_in_passive:                     0
% 1.34/0.99  res_num_in_active:                      0
% 1.34/0.99  res_num_of_loops:                       69
% 1.34/0.99  res_forward_subset_subsumed:            7
% 1.34/0.99  res_backward_subset_subsumed:           0
% 1.34/0.99  res_forward_subsumed:                   0
% 1.34/0.99  res_backward_subsumed:                  0
% 1.34/0.99  res_forward_subsumption_resolution:     1
% 1.34/0.99  res_backward_subsumption_resolution:    0
% 1.34/0.99  res_clause_to_clause_subsumption:       141
% 1.34/0.99  res_orphan_elimination:                 0
% 1.34/0.99  res_tautology_del:                      12
% 1.34/0.99  res_num_eq_res_simplified:              0
% 1.34/0.99  res_num_sel_changes:                    0
% 1.34/0.99  res_moves_from_active_to_pass:          0
% 1.34/0.99  
% 1.34/0.99  ------ Superposition
% 1.34/0.99  
% 1.34/0.99  sup_time_total:                         0.
% 1.34/0.99  sup_time_generating:                    0.
% 1.34/0.99  sup_time_sim_full:                      0.
% 1.34/0.99  sup_time_sim_immed:                     0.
% 1.34/0.99  
% 1.34/0.99  sup_num_of_clauses:                     21
% 1.34/0.99  sup_num_in_active:                      16
% 1.34/0.99  sup_num_in_passive:                     5
% 1.34/0.99  sup_num_of_loops:                       15
% 1.34/0.99  sup_fw_superposition:                   6
% 1.34/0.99  sup_bw_superposition:                   12
% 1.34/0.99  sup_immediate_simplified:               6
% 1.34/0.99  sup_given_eliminated:                   0
% 1.34/0.99  comparisons_done:                       0
% 1.34/0.99  comparisons_avoided:                    0
% 1.34/0.99  
% 1.34/0.99  ------ Simplifications
% 1.34/0.99  
% 1.34/0.99  
% 1.34/0.99  sim_fw_subset_subsumed:                 1
% 1.34/0.99  sim_bw_subset_subsumed:                 0
% 1.34/0.99  sim_fw_subsumed:                        4
% 1.34/0.99  sim_bw_subsumed:                        0
% 1.34/0.99  sim_fw_subsumption_res:                 1
% 1.34/0.99  sim_bw_subsumption_res:                 1
% 1.34/0.99  sim_tautology_del:                      2
% 1.34/0.99  sim_eq_tautology_del:                   1
% 1.34/0.99  sim_eq_res_simp:                        0
% 1.34/0.99  sim_fw_demodulated:                     0
% 1.34/0.99  sim_bw_demodulated:                     0
% 1.34/0.99  sim_light_normalised:                   1
% 1.34/0.99  sim_joinable_taut:                      0
% 1.34/0.99  sim_joinable_simp:                      0
% 1.34/0.99  sim_ac_normalised:                      0
% 1.34/0.99  sim_smt_subsumption:                    0
% 1.34/0.99  
%------------------------------------------------------------------------------
