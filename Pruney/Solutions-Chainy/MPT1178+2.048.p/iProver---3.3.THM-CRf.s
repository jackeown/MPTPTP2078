%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:07 EST 2020

% Result     : Theorem 0.96s
% Output     : CNFRefutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 322 expanded)
%              Number of clauses        :   54 (  80 expanded)
%              Number of leaves         :   16 (  90 expanded)
%              Depth                    :   21
%              Number of atoms          :  474 (1858 expanded)
%              Number of equality atoms :  103 ( 327 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
     => m2_orders_2(sK1(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK1(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f28])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK1(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK4))
        & m1_orders_1(sK4,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK3,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK3))) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4))
    & m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3)))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f33,f32])).

fof(f53,plain,(
    m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK2(X0),X0)
        & k1_xboole_0 != sK2(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK2(X0),X0)
          & k1_xboole_0 != sK2(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f30])).

fof(f45,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X3] :
                    ( ( r2_hidden(X3,X2)
                      | ~ m2_orders_2(X3,X0,X1) )
                    & ( m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK0(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( m2_orders_2(sK0(X0,X1,X2),X0,X1)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK0(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK0(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK0(X0,X1,X2),X0,X1)
                    | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ m2_orders_2(X4,X0,X1)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m2_orders_2(X4,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f54,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_8,plain,
    ( m2_orders_2(sK1(X0,X1),X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,negated_conjecture,
    ( m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_249,plain,
    ( m2_orders_2(sK1(X0,X1),X0,X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_250,plain,
    ( m2_orders_2(sK1(X0,sK4),X0,sK4)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_249])).

cnf(c_15,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_535,plain,
    ( m2_orders_2(sK1(X0,sK4),X0,sK4)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_250,c_15])).

cnf(c_536,plain,
    ( m2_orders_2(sK1(sK3,sK4),sK3,sK4)
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_18,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_17,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_16,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_538,plain,
    ( m2_orders_2(sK1(sK3,sK4),sK3,sK4)
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_19,c_18,c_17,c_16])).

cnf(c_981,plain,
    ( m2_orders_2(sK1(sK3,sK4),sK3,sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_538])).

cnf(c_1295,plain,
    ( m2_orders_2(sK1(sK3,sK4),sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_981])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_6,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_402,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_403,plain,
    ( ~ m2_orders_2(X0,X1,sK4)
    | r2_hidden(X0,k4_orders_2(X1,sK4))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_549,plain,
    ( ~ m2_orders_2(X0,X1,sK4)
    | r2_hidden(X0,k4_orders_2(X1,sK4))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_403,c_15])).

cnf(c_550,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(X0,k4_orders_2(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_554,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(X0,k4_orders_2(sK3,sK4))
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_550,c_19,c_18,c_17,c_16])).

cnf(c_777,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | X0 != X1
    | k4_orders_2(sK3,sK4) != X2
    | k3_tarski(X2) != k1_xboole_0
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3))
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_554])).

cnf(c_778,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | k3_tarski(k4_orders_2(sK3,sK4)) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_1307,plain,
    ( k3_tarski(k4_orders_2(sK3,sK4)) != k1_xboole_0
    | k1_xboole_0 = X0
    | m2_orders_2(X0,sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1350,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0
    | m2_orders_2(X0,sK3,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1307,c_13])).

cnf(c_1351,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK3,sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1350])).

cnf(c_1423,plain,
    ( sK1(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1295,c_1351])).

cnf(c_1425,plain,
    ( m2_orders_2(k1_xboole_0,sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1423,c_1295])).

cnf(c_1047,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1068,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_1049,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1058,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_208,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_209,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_208])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_219,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_220,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_219])).

cnf(c_234,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_209,c_220])).

cnf(c_235,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_9,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_342,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_343,plain,
    ( ~ m2_orders_2(X0,X1,sK4)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_591,plain,
    ( ~ m2_orders_2(X0,X1,sK4)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_343,c_15])).

cnf(c_592,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X0)
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_596,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X0)
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_592,c_19,c_18,c_17,c_16])).

cnf(c_874,plain,
    ( ~ m2_orders_2(X0,sK3,sK4)
    | k1_funct_1(sK4,u1_struct_0(sK3)) != X1
    | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3))
    | k1_zfmisc_1(X2) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_235,c_596])).

cnf(c_875,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK3,sK4)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_874])).

cnf(c_876,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(k1_xboole_0)
    | m2_orders_2(k1_xboole_0,sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_875])).

cnf(c_878,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | m2_orders_2(k1_xboole_0,sK3,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1425,c_1068,c_1058,c_878])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:10:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 0.96/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.96/1.04  
% 0.96/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.96/1.04  
% 0.96/1.04  ------  iProver source info
% 0.96/1.04  
% 0.96/1.04  git: date: 2020-06-30 10:37:57 +0100
% 0.96/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.96/1.04  git: non_committed_changes: false
% 0.96/1.04  git: last_make_outside_of_git: false
% 0.96/1.04  
% 0.96/1.04  ------ 
% 0.96/1.04  
% 0.96/1.04  ------ Input Options
% 0.96/1.04  
% 0.96/1.04  --out_options                           all
% 0.96/1.04  --tptp_safe_out                         true
% 0.96/1.04  --problem_path                          ""
% 0.96/1.04  --include_path                          ""
% 0.96/1.04  --clausifier                            res/vclausify_rel
% 0.96/1.04  --clausifier_options                    --mode clausify
% 0.96/1.04  --stdin                                 false
% 0.96/1.04  --stats_out                             all
% 0.96/1.04  
% 0.96/1.04  ------ General Options
% 0.96/1.04  
% 0.96/1.04  --fof                                   false
% 0.96/1.04  --time_out_real                         305.
% 0.96/1.04  --time_out_virtual                      -1.
% 0.96/1.04  --symbol_type_check                     false
% 0.96/1.04  --clausify_out                          false
% 0.96/1.04  --sig_cnt_out                           false
% 0.96/1.04  --trig_cnt_out                          false
% 0.96/1.04  --trig_cnt_out_tolerance                1.
% 0.96/1.04  --trig_cnt_out_sk_spl                   false
% 0.96/1.04  --abstr_cl_out                          false
% 0.96/1.04  
% 0.96/1.04  ------ Global Options
% 0.96/1.04  
% 0.96/1.04  --schedule                              default
% 0.96/1.04  --add_important_lit                     false
% 0.96/1.04  --prop_solver_per_cl                    1000
% 0.96/1.04  --min_unsat_core                        false
% 0.96/1.04  --soft_assumptions                      false
% 0.96/1.04  --soft_lemma_size                       3
% 0.96/1.04  --prop_impl_unit_size                   0
% 0.96/1.04  --prop_impl_unit                        []
% 0.96/1.04  --share_sel_clauses                     true
% 0.96/1.04  --reset_solvers                         false
% 0.96/1.04  --bc_imp_inh                            [conj_cone]
% 0.96/1.04  --conj_cone_tolerance                   3.
% 0.96/1.04  --extra_neg_conj                        none
% 0.96/1.04  --large_theory_mode                     true
% 0.96/1.04  --prolific_symb_bound                   200
% 0.96/1.04  --lt_threshold                          2000
% 0.96/1.04  --clause_weak_htbl                      true
% 0.96/1.04  --gc_record_bc_elim                     false
% 0.96/1.04  
% 0.96/1.04  ------ Preprocessing Options
% 0.96/1.04  
% 0.96/1.04  --preprocessing_flag                    true
% 0.96/1.04  --time_out_prep_mult                    0.1
% 0.96/1.04  --splitting_mode                        input
% 0.96/1.04  --splitting_grd                         true
% 0.96/1.04  --splitting_cvd                         false
% 0.96/1.04  --splitting_cvd_svl                     false
% 0.96/1.04  --splitting_nvd                         32
% 0.96/1.04  --sub_typing                            true
% 0.96/1.04  --prep_gs_sim                           true
% 0.96/1.04  --prep_unflatten                        true
% 0.96/1.04  --prep_res_sim                          true
% 0.96/1.04  --prep_upred                            true
% 0.96/1.04  --prep_sem_filter                       exhaustive
% 0.96/1.04  --prep_sem_filter_out                   false
% 0.96/1.04  --pred_elim                             true
% 0.96/1.04  --res_sim_input                         true
% 0.96/1.04  --eq_ax_congr_red                       true
% 0.96/1.04  --pure_diseq_elim                       true
% 0.96/1.04  --brand_transform                       false
% 0.96/1.04  --non_eq_to_eq                          false
% 0.96/1.04  --prep_def_merge                        true
% 0.96/1.04  --prep_def_merge_prop_impl              false
% 0.96/1.04  --prep_def_merge_mbd                    true
% 0.96/1.04  --prep_def_merge_tr_red                 false
% 0.96/1.04  --prep_def_merge_tr_cl                  false
% 0.96/1.04  --smt_preprocessing                     true
% 0.96/1.04  --smt_ac_axioms                         fast
% 0.96/1.04  --preprocessed_out                      false
% 0.96/1.04  --preprocessed_stats                    false
% 0.96/1.04  
% 0.96/1.04  ------ Abstraction refinement Options
% 0.96/1.04  
% 0.96/1.04  --abstr_ref                             []
% 0.96/1.04  --abstr_ref_prep                        false
% 0.96/1.04  --abstr_ref_until_sat                   false
% 0.96/1.04  --abstr_ref_sig_restrict                funpre
% 0.96/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.96/1.04  --abstr_ref_under                       []
% 0.96/1.04  
% 0.96/1.04  ------ SAT Options
% 0.96/1.04  
% 0.96/1.04  --sat_mode                              false
% 0.96/1.04  --sat_fm_restart_options                ""
% 0.96/1.04  --sat_gr_def                            false
% 0.96/1.04  --sat_epr_types                         true
% 0.96/1.04  --sat_non_cyclic_types                  false
% 0.96/1.04  --sat_finite_models                     false
% 0.96/1.04  --sat_fm_lemmas                         false
% 0.96/1.04  --sat_fm_prep                           false
% 0.96/1.04  --sat_fm_uc_incr                        true
% 0.96/1.04  --sat_out_model                         small
% 0.96/1.04  --sat_out_clauses                       false
% 0.96/1.04  
% 0.96/1.04  ------ QBF Options
% 0.96/1.04  
% 0.96/1.04  --qbf_mode                              false
% 0.96/1.04  --qbf_elim_univ                         false
% 0.96/1.04  --qbf_dom_inst                          none
% 0.96/1.04  --qbf_dom_pre_inst                      false
% 0.96/1.04  --qbf_sk_in                             false
% 0.96/1.04  --qbf_pred_elim                         true
% 0.96/1.04  --qbf_split                             512
% 0.96/1.04  
% 0.96/1.04  ------ BMC1 Options
% 0.96/1.04  
% 0.96/1.04  --bmc1_incremental                      false
% 0.96/1.04  --bmc1_axioms                           reachable_all
% 0.96/1.04  --bmc1_min_bound                        0
% 0.96/1.04  --bmc1_max_bound                        -1
% 0.96/1.04  --bmc1_max_bound_default                -1
% 0.96/1.04  --bmc1_symbol_reachability              true
% 0.96/1.04  --bmc1_property_lemmas                  false
% 0.96/1.04  --bmc1_k_induction                      false
% 0.96/1.04  --bmc1_non_equiv_states                 false
% 0.96/1.04  --bmc1_deadlock                         false
% 0.96/1.04  --bmc1_ucm                              false
% 0.96/1.04  --bmc1_add_unsat_core                   none
% 0.96/1.04  --bmc1_unsat_core_children              false
% 0.96/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.96/1.04  --bmc1_out_stat                         full
% 0.96/1.04  --bmc1_ground_init                      false
% 0.96/1.04  --bmc1_pre_inst_next_state              false
% 0.96/1.04  --bmc1_pre_inst_state                   false
% 0.96/1.04  --bmc1_pre_inst_reach_state             false
% 0.96/1.04  --bmc1_out_unsat_core                   false
% 0.96/1.04  --bmc1_aig_witness_out                  false
% 0.96/1.04  --bmc1_verbose                          false
% 0.96/1.04  --bmc1_dump_clauses_tptp                false
% 0.96/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.96/1.04  --bmc1_dump_file                        -
% 0.96/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.96/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.96/1.04  --bmc1_ucm_extend_mode                  1
% 0.96/1.04  --bmc1_ucm_init_mode                    2
% 0.96/1.04  --bmc1_ucm_cone_mode                    none
% 0.96/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.96/1.04  --bmc1_ucm_relax_model                  4
% 0.96/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.96/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.96/1.04  --bmc1_ucm_layered_model                none
% 0.96/1.04  --bmc1_ucm_max_lemma_size               10
% 0.96/1.04  
% 0.96/1.04  ------ AIG Options
% 0.96/1.04  
% 0.96/1.04  --aig_mode                              false
% 0.96/1.04  
% 0.96/1.04  ------ Instantiation Options
% 0.96/1.04  
% 0.96/1.04  --instantiation_flag                    true
% 0.96/1.04  --inst_sos_flag                         false
% 0.96/1.04  --inst_sos_phase                        true
% 0.96/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.96/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.96/1.04  --inst_lit_sel_side                     num_symb
% 0.96/1.04  --inst_solver_per_active                1400
% 0.96/1.04  --inst_solver_calls_frac                1.
% 0.96/1.04  --inst_passive_queue_type               priority_queues
% 0.96/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.96/1.04  --inst_passive_queues_freq              [25;2]
% 0.96/1.04  --inst_dismatching                      true
% 0.96/1.04  --inst_eager_unprocessed_to_passive     true
% 0.96/1.04  --inst_prop_sim_given                   true
% 0.96/1.04  --inst_prop_sim_new                     false
% 0.96/1.04  --inst_subs_new                         false
% 0.96/1.04  --inst_eq_res_simp                      false
% 0.96/1.04  --inst_subs_given                       false
% 0.96/1.04  --inst_orphan_elimination               true
% 0.96/1.04  --inst_learning_loop_flag               true
% 0.96/1.04  --inst_learning_start                   3000
% 0.96/1.04  --inst_learning_factor                  2
% 0.96/1.04  --inst_start_prop_sim_after_learn       3
% 0.96/1.04  --inst_sel_renew                        solver
% 0.96/1.04  --inst_lit_activity_flag                true
% 0.96/1.04  --inst_restr_to_given                   false
% 0.96/1.04  --inst_activity_threshold               500
% 0.96/1.04  --inst_out_proof                        true
% 0.96/1.04  
% 0.96/1.04  ------ Resolution Options
% 0.96/1.04  
% 0.96/1.04  --resolution_flag                       true
% 0.96/1.04  --res_lit_sel                           adaptive
% 0.96/1.04  --res_lit_sel_side                      none
% 0.96/1.04  --res_ordering                          kbo
% 0.96/1.04  --res_to_prop_solver                    active
% 0.96/1.04  --res_prop_simpl_new                    false
% 0.96/1.04  --res_prop_simpl_given                  true
% 0.96/1.04  --res_passive_queue_type                priority_queues
% 0.96/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.96/1.04  --res_passive_queues_freq               [15;5]
% 0.96/1.04  --res_forward_subs                      full
% 0.96/1.04  --res_backward_subs                     full
% 0.96/1.04  --res_forward_subs_resolution           true
% 0.96/1.04  --res_backward_subs_resolution          true
% 0.96/1.04  --res_orphan_elimination                true
% 0.96/1.04  --res_time_limit                        2.
% 0.96/1.04  --res_out_proof                         true
% 0.96/1.04  
% 0.96/1.04  ------ Superposition Options
% 0.96/1.04  
% 0.96/1.04  --superposition_flag                    true
% 0.96/1.04  --sup_passive_queue_type                priority_queues
% 0.96/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.96/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.96/1.04  --demod_completeness_check              fast
% 0.96/1.04  --demod_use_ground                      true
% 0.96/1.04  --sup_to_prop_solver                    passive
% 0.96/1.04  --sup_prop_simpl_new                    true
% 0.96/1.04  --sup_prop_simpl_given                  true
% 0.96/1.04  --sup_fun_splitting                     false
% 0.96/1.04  --sup_smt_interval                      50000
% 0.96/1.04  
% 0.96/1.04  ------ Superposition Simplification Setup
% 0.96/1.04  
% 0.96/1.04  --sup_indices_passive                   []
% 0.96/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.96/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/1.04  --sup_full_bw                           [BwDemod]
% 0.96/1.04  --sup_immed_triv                        [TrivRules]
% 0.96/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.96/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/1.04  --sup_immed_bw_main                     []
% 0.96/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.96/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/1.04  
% 0.96/1.04  ------ Combination Options
% 0.96/1.04  
% 0.96/1.04  --comb_res_mult                         3
% 0.96/1.04  --comb_sup_mult                         2
% 0.96/1.04  --comb_inst_mult                        10
% 0.96/1.04  
% 0.96/1.04  ------ Debug Options
% 0.96/1.04  
% 0.96/1.04  --dbg_backtrace                         false
% 0.96/1.04  --dbg_dump_prop_clauses                 false
% 0.96/1.04  --dbg_dump_prop_clauses_file            -
% 0.96/1.04  --dbg_out_stat                          false
% 0.96/1.04  ------ Parsing...
% 0.96/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.96/1.04  
% 0.96/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 0.96/1.04  
% 0.96/1.04  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.96/1.04  
% 0.96/1.04  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.96/1.04  ------ Proving...
% 0.96/1.04  ------ Problem Properties 
% 0.96/1.04  
% 0.96/1.04  
% 0.96/1.04  clauses                                 17
% 0.96/1.04  conjectures                             1
% 0.96/1.04  EPR                                     1
% 0.96/1.04  Horn                                    12
% 0.96/1.04  unary                                   2
% 0.96/1.04  binary                                  8
% 0.96/1.04  lits                                    42
% 0.96/1.04  lits eq                                 23
% 0.96/1.04  fd_pure                                 0
% 0.96/1.04  fd_pseudo                               0
% 0.96/1.04  fd_cond                                 4
% 0.96/1.04  fd_pseudo_cond                          0
% 0.96/1.04  AC symbols                              0
% 0.96/1.04  
% 0.96/1.04  ------ Schedule dynamic 5 is on 
% 0.96/1.04  
% 0.96/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.96/1.04  
% 0.96/1.04  
% 0.96/1.04  ------ 
% 0.96/1.04  Current options:
% 0.96/1.04  ------ 
% 0.96/1.04  
% 0.96/1.04  ------ Input Options
% 0.96/1.04  
% 0.96/1.04  --out_options                           all
% 0.96/1.04  --tptp_safe_out                         true
% 0.96/1.04  --problem_path                          ""
% 0.96/1.04  --include_path                          ""
% 0.96/1.04  --clausifier                            res/vclausify_rel
% 0.96/1.04  --clausifier_options                    --mode clausify
% 0.96/1.04  --stdin                                 false
% 0.96/1.04  --stats_out                             all
% 0.96/1.04  
% 0.96/1.04  ------ General Options
% 0.96/1.04  
% 0.96/1.04  --fof                                   false
% 0.96/1.04  --time_out_real                         305.
% 0.96/1.04  --time_out_virtual                      -1.
% 0.96/1.04  --symbol_type_check                     false
% 0.96/1.04  --clausify_out                          false
% 0.96/1.04  --sig_cnt_out                           false
% 0.96/1.04  --trig_cnt_out                          false
% 0.96/1.04  --trig_cnt_out_tolerance                1.
% 0.96/1.04  --trig_cnt_out_sk_spl                   false
% 0.96/1.04  --abstr_cl_out                          false
% 0.96/1.04  
% 0.96/1.04  ------ Global Options
% 0.96/1.04  
% 0.96/1.04  --schedule                              default
% 0.96/1.04  --add_important_lit                     false
% 0.96/1.04  --prop_solver_per_cl                    1000
% 0.96/1.04  --min_unsat_core                        false
% 0.96/1.04  --soft_assumptions                      false
% 0.96/1.04  --soft_lemma_size                       3
% 0.96/1.04  --prop_impl_unit_size                   0
% 0.96/1.04  --prop_impl_unit                        []
% 0.96/1.04  --share_sel_clauses                     true
% 0.96/1.04  --reset_solvers                         false
% 0.96/1.04  --bc_imp_inh                            [conj_cone]
% 0.96/1.04  --conj_cone_tolerance                   3.
% 0.96/1.04  --extra_neg_conj                        none
% 0.96/1.04  --large_theory_mode                     true
% 0.96/1.04  --prolific_symb_bound                   200
% 0.96/1.04  --lt_threshold                          2000
% 0.96/1.04  --clause_weak_htbl                      true
% 0.96/1.04  --gc_record_bc_elim                     false
% 0.96/1.04  
% 0.96/1.04  ------ Preprocessing Options
% 0.96/1.04  
% 0.96/1.04  --preprocessing_flag                    true
% 0.96/1.04  --time_out_prep_mult                    0.1
% 0.96/1.04  --splitting_mode                        input
% 0.96/1.04  --splitting_grd                         true
% 0.96/1.04  --splitting_cvd                         false
% 0.96/1.04  --splitting_cvd_svl                     false
% 0.96/1.04  --splitting_nvd                         32
% 0.96/1.04  --sub_typing                            true
% 0.96/1.04  --prep_gs_sim                           true
% 0.96/1.04  --prep_unflatten                        true
% 0.96/1.04  --prep_res_sim                          true
% 0.96/1.04  --prep_upred                            true
% 0.96/1.04  --prep_sem_filter                       exhaustive
% 0.96/1.04  --prep_sem_filter_out                   false
% 0.96/1.04  --pred_elim                             true
% 0.96/1.04  --res_sim_input                         true
% 0.96/1.04  --eq_ax_congr_red                       true
% 0.96/1.04  --pure_diseq_elim                       true
% 0.96/1.04  --brand_transform                       false
% 0.96/1.04  --non_eq_to_eq                          false
% 0.96/1.04  --prep_def_merge                        true
% 0.96/1.04  --prep_def_merge_prop_impl              false
% 0.96/1.04  --prep_def_merge_mbd                    true
% 0.96/1.04  --prep_def_merge_tr_red                 false
% 0.96/1.04  --prep_def_merge_tr_cl                  false
% 0.96/1.04  --smt_preprocessing                     true
% 0.96/1.04  --smt_ac_axioms                         fast
% 0.96/1.04  --preprocessed_out                      false
% 0.96/1.04  --preprocessed_stats                    false
% 0.96/1.04  
% 0.96/1.04  ------ Abstraction refinement Options
% 0.96/1.04  
% 0.96/1.04  --abstr_ref                             []
% 0.96/1.04  --abstr_ref_prep                        false
% 0.96/1.04  --abstr_ref_until_sat                   false
% 0.96/1.04  --abstr_ref_sig_restrict                funpre
% 0.96/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.96/1.04  --abstr_ref_under                       []
% 0.96/1.04  
% 0.96/1.04  ------ SAT Options
% 0.96/1.04  
% 0.96/1.04  --sat_mode                              false
% 0.96/1.04  --sat_fm_restart_options                ""
% 0.96/1.04  --sat_gr_def                            false
% 0.96/1.04  --sat_epr_types                         true
% 0.96/1.04  --sat_non_cyclic_types                  false
% 0.96/1.04  --sat_finite_models                     false
% 0.96/1.04  --sat_fm_lemmas                         false
% 0.96/1.04  --sat_fm_prep                           false
% 0.96/1.04  --sat_fm_uc_incr                        true
% 0.96/1.04  --sat_out_model                         small
% 0.96/1.04  --sat_out_clauses                       false
% 0.96/1.04  
% 0.96/1.04  ------ QBF Options
% 0.96/1.04  
% 0.96/1.04  --qbf_mode                              false
% 0.96/1.04  --qbf_elim_univ                         false
% 0.96/1.04  --qbf_dom_inst                          none
% 0.96/1.04  --qbf_dom_pre_inst                      false
% 0.96/1.04  --qbf_sk_in                             false
% 0.96/1.04  --qbf_pred_elim                         true
% 0.96/1.04  --qbf_split                             512
% 0.96/1.04  
% 0.96/1.04  ------ BMC1 Options
% 0.96/1.04  
% 0.96/1.04  --bmc1_incremental                      false
% 0.96/1.04  --bmc1_axioms                           reachable_all
% 0.96/1.04  --bmc1_min_bound                        0
% 0.96/1.04  --bmc1_max_bound                        -1
% 0.96/1.04  --bmc1_max_bound_default                -1
% 0.96/1.04  --bmc1_symbol_reachability              true
% 0.96/1.04  --bmc1_property_lemmas                  false
% 0.96/1.04  --bmc1_k_induction                      false
% 0.96/1.04  --bmc1_non_equiv_states                 false
% 0.96/1.04  --bmc1_deadlock                         false
% 0.96/1.04  --bmc1_ucm                              false
% 0.96/1.04  --bmc1_add_unsat_core                   none
% 0.96/1.04  --bmc1_unsat_core_children              false
% 0.96/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.96/1.04  --bmc1_out_stat                         full
% 0.96/1.04  --bmc1_ground_init                      false
% 0.96/1.04  --bmc1_pre_inst_next_state              false
% 0.96/1.04  --bmc1_pre_inst_state                   false
% 0.96/1.04  --bmc1_pre_inst_reach_state             false
% 0.96/1.04  --bmc1_out_unsat_core                   false
% 0.96/1.04  --bmc1_aig_witness_out                  false
% 0.96/1.04  --bmc1_verbose                          false
% 0.96/1.04  --bmc1_dump_clauses_tptp                false
% 0.96/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.96/1.04  --bmc1_dump_file                        -
% 0.96/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.96/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.96/1.04  --bmc1_ucm_extend_mode                  1
% 0.96/1.04  --bmc1_ucm_init_mode                    2
% 0.96/1.04  --bmc1_ucm_cone_mode                    none
% 0.96/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.96/1.04  --bmc1_ucm_relax_model                  4
% 0.96/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.96/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.96/1.04  --bmc1_ucm_layered_model                none
% 0.96/1.04  --bmc1_ucm_max_lemma_size               10
% 0.96/1.04  
% 0.96/1.04  ------ AIG Options
% 0.96/1.04  
% 0.96/1.04  --aig_mode                              false
% 0.96/1.04  
% 0.96/1.04  ------ Instantiation Options
% 0.96/1.04  
% 0.96/1.04  --instantiation_flag                    true
% 0.96/1.04  --inst_sos_flag                         false
% 0.96/1.04  --inst_sos_phase                        true
% 0.96/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.96/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.96/1.04  --inst_lit_sel_side                     none
% 0.96/1.04  --inst_solver_per_active                1400
% 0.96/1.04  --inst_solver_calls_frac                1.
% 0.96/1.04  --inst_passive_queue_type               priority_queues
% 0.96/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.96/1.04  --inst_passive_queues_freq              [25;2]
% 0.96/1.04  --inst_dismatching                      true
% 0.96/1.04  --inst_eager_unprocessed_to_passive     true
% 0.96/1.04  --inst_prop_sim_given                   true
% 0.96/1.04  --inst_prop_sim_new                     false
% 0.96/1.04  --inst_subs_new                         false
% 0.96/1.04  --inst_eq_res_simp                      false
% 0.96/1.04  --inst_subs_given                       false
% 0.96/1.04  --inst_orphan_elimination               true
% 0.96/1.04  --inst_learning_loop_flag               true
% 0.96/1.04  --inst_learning_start                   3000
% 0.96/1.04  --inst_learning_factor                  2
% 0.96/1.04  --inst_start_prop_sim_after_learn       3
% 0.96/1.04  --inst_sel_renew                        solver
% 0.96/1.04  --inst_lit_activity_flag                true
% 0.96/1.04  --inst_restr_to_given                   false
% 0.96/1.04  --inst_activity_threshold               500
% 0.96/1.04  --inst_out_proof                        true
% 0.96/1.04  
% 0.96/1.04  ------ Resolution Options
% 0.96/1.04  
% 0.96/1.04  --resolution_flag                       false
% 0.96/1.04  --res_lit_sel                           adaptive
% 0.96/1.04  --res_lit_sel_side                      none
% 0.96/1.04  --res_ordering                          kbo
% 0.96/1.04  --res_to_prop_solver                    active
% 0.96/1.04  --res_prop_simpl_new                    false
% 0.96/1.04  --res_prop_simpl_given                  true
% 0.96/1.04  --res_passive_queue_type                priority_queues
% 0.96/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.96/1.04  --res_passive_queues_freq               [15;5]
% 0.96/1.04  --res_forward_subs                      full
% 0.96/1.04  --res_backward_subs                     full
% 0.96/1.04  --res_forward_subs_resolution           true
% 0.96/1.04  --res_backward_subs_resolution          true
% 0.96/1.04  --res_orphan_elimination                true
% 0.96/1.04  --res_time_limit                        2.
% 0.96/1.04  --res_out_proof                         true
% 0.96/1.04  
% 0.96/1.04  ------ Superposition Options
% 0.96/1.04  
% 0.96/1.04  --superposition_flag                    true
% 0.96/1.04  --sup_passive_queue_type                priority_queues
% 0.96/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.96/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.96/1.04  --demod_completeness_check              fast
% 0.96/1.04  --demod_use_ground                      true
% 0.96/1.04  --sup_to_prop_solver                    passive
% 0.96/1.04  --sup_prop_simpl_new                    true
% 0.96/1.04  --sup_prop_simpl_given                  true
% 0.96/1.04  --sup_fun_splitting                     false
% 0.96/1.04  --sup_smt_interval                      50000
% 0.96/1.04  
% 0.96/1.04  ------ Superposition Simplification Setup
% 0.96/1.04  
% 0.96/1.04  --sup_indices_passive                   []
% 0.96/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.96/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/1.04  --sup_full_bw                           [BwDemod]
% 0.96/1.04  --sup_immed_triv                        [TrivRules]
% 0.96/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.96/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/1.04  --sup_immed_bw_main                     []
% 0.96/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.96/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/1.04  
% 0.96/1.04  ------ Combination Options
% 0.96/1.04  
% 0.96/1.04  --comb_res_mult                         3
% 0.96/1.04  --comb_sup_mult                         2
% 0.96/1.04  --comb_inst_mult                        10
% 0.96/1.04  
% 0.96/1.04  ------ Debug Options
% 0.96/1.04  
% 0.96/1.04  --dbg_backtrace                         false
% 0.96/1.04  --dbg_dump_prop_clauses                 false
% 0.96/1.04  --dbg_dump_prop_clauses_file            -
% 0.96/1.04  --dbg_out_stat                          false
% 0.96/1.04  
% 0.96/1.04  
% 0.96/1.04  
% 0.96/1.04  
% 0.96/1.04  ------ Proving...
% 0.96/1.04  
% 0.96/1.04  
% 0.96/1.04  % SZS status Theorem for theBenchmark.p
% 0.96/1.04  
% 0.96/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.96/1.04  
% 0.96/1.04  fof(f6,axiom,(
% 0.96/1.04    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 0.96/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.04  
% 0.96/1.04  fof(f17,plain,(
% 0.96/1.04    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.96/1.04    inference(ennf_transformation,[],[f6])).
% 0.96/1.04  
% 0.96/1.04  fof(f18,plain,(
% 0.96/1.04    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.96/1.04    inference(flattening,[],[f17])).
% 0.96/1.04  
% 0.96/1.04  fof(f28,plain,(
% 0.96/1.04    ! [X1,X0] : (? [X2] : m2_orders_2(X2,X0,X1) => m2_orders_2(sK1(X0,X1),X0,X1))),
% 0.96/1.04    introduced(choice_axiom,[])).
% 0.96/1.04  
% 0.96/1.04  fof(f29,plain,(
% 0.96/1.04    ! [X0,X1] : (m2_orders_2(sK1(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.96/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f28])).
% 0.96/1.04  
% 0.96/1.04  fof(f43,plain,(
% 0.96/1.04    ( ! [X0,X1] : (m2_orders_2(sK1(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.96/1.04    inference(cnf_transformation,[],[f29])).
% 0.96/1.04  
% 0.96/1.04  fof(f9,conjecture,(
% 0.96/1.04    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.96/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.04  
% 0.96/1.04  fof(f10,negated_conjecture,(
% 0.96/1.04    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.96/1.04    inference(negated_conjecture,[],[f9])).
% 0.96/1.04  
% 0.96/1.04  fof(f22,plain,(
% 0.96/1.04    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.96/1.04    inference(ennf_transformation,[],[f10])).
% 0.96/1.04  
% 0.96/1.04  fof(f23,plain,(
% 0.96/1.04    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.96/1.04    inference(flattening,[],[f22])).
% 0.96/1.04  
% 0.96/1.04  fof(f33,plain,(
% 0.96/1.04    ( ! [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK4)) & m1_orders_1(sK4,k1_orders_1(u1_struct_0(X0))))) )),
% 0.96/1.04    introduced(choice_axiom,[])).
% 0.96/1.04  
% 0.96/1.04  fof(f32,plain,(
% 0.96/1.04    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK3,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK3)))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 0.96/1.04    introduced(choice_axiom,[])).
% 0.96/1.04  
% 0.96/1.04  fof(f34,plain,(
% 0.96/1.04    (k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) & m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3)))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 0.96/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f33,f32])).
% 0.96/1.04  
% 0.96/1.04  fof(f53,plain,(
% 0.96/1.04    m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3)))),
% 0.96/1.04    inference(cnf_transformation,[],[f34])).
% 0.96/1.04  
% 0.96/1.04  fof(f52,plain,(
% 0.96/1.04    l1_orders_2(sK3)),
% 0.96/1.04    inference(cnf_transformation,[],[f34])).
% 0.96/1.04  
% 0.96/1.04  fof(f48,plain,(
% 0.96/1.04    ~v2_struct_0(sK3)),
% 0.96/1.04    inference(cnf_transformation,[],[f34])).
% 0.96/1.04  
% 0.96/1.04  fof(f49,plain,(
% 0.96/1.04    v3_orders_2(sK3)),
% 0.96/1.04    inference(cnf_transformation,[],[f34])).
% 0.96/1.04  
% 0.96/1.04  fof(f50,plain,(
% 0.96/1.04    v4_orders_2(sK3)),
% 0.96/1.04    inference(cnf_transformation,[],[f34])).
% 0.96/1.04  
% 0.96/1.04  fof(f51,plain,(
% 0.96/1.04    v5_orders_2(sK3)),
% 0.96/1.04    inference(cnf_transformation,[],[f34])).
% 0.96/1.04  
% 0.96/1.04  fof(f8,axiom,(
% 0.96/1.04    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.96/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.04  
% 0.96/1.04  fof(f11,plain,(
% 0.96/1.04    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.96/1.04    inference(rectify,[],[f8])).
% 0.96/1.04  
% 0.96/1.04  fof(f21,plain,(
% 0.96/1.04    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.96/1.04    inference(ennf_transformation,[],[f11])).
% 0.96/1.04  
% 0.96/1.04  fof(f30,plain,(
% 0.96/1.04    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)))),
% 0.96/1.04    introduced(choice_axiom,[])).
% 0.96/1.04  
% 0.96/1.04  fof(f31,plain,(
% 0.96/1.04    ! [X0] : (((r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.96/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f30])).
% 0.96/1.04  
% 0.96/1.04  fof(f45,plain,(
% 0.96/1.04    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 0.96/1.04    inference(cnf_transformation,[],[f31])).
% 0.96/1.04  
% 0.96/1.04  fof(f5,axiom,(
% 0.96/1.04    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.96/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.04  
% 0.96/1.04  fof(f15,plain,(
% 0.96/1.04    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.96/1.04    inference(ennf_transformation,[],[f5])).
% 0.96/1.04  
% 0.96/1.04  fof(f16,plain,(
% 0.96/1.04    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.96/1.04    inference(flattening,[],[f15])).
% 0.96/1.04  
% 0.96/1.04  fof(f24,plain,(
% 0.96/1.04    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.96/1.04    inference(nnf_transformation,[],[f16])).
% 0.96/1.04  
% 0.96/1.04  fof(f25,plain,(
% 0.96/1.04    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.96/1.04    inference(rectify,[],[f24])).
% 0.96/1.04  
% 0.96/1.04  fof(f26,plain,(
% 0.96/1.04    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK0(X0,X1,X2),X0,X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (m2_orders_2(sK0(X0,X1,X2),X0,X1) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 0.96/1.04    introduced(choice_axiom,[])).
% 0.96/1.04  
% 0.96/1.04  fof(f27,plain,(
% 0.96/1.04    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK0(X0,X1,X2),X0,X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (m2_orders_2(sK0(X0,X1,X2),X0,X1) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.96/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 0.96/1.04  
% 0.96/1.04  fof(f40,plain,(
% 0.96/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.96/1.04    inference(cnf_transformation,[],[f27])).
% 0.96/1.04  
% 0.96/1.04  fof(f55,plain,(
% 0.96/1.04    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_orders_2(X0,X1)) | ~m2_orders_2(X4,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.96/1.04    inference(equality_resolution,[],[f40])).
% 0.96/1.04  
% 0.96/1.04  fof(f54,plain,(
% 0.96/1.04    k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4))),
% 0.96/1.04    inference(cnf_transformation,[],[f34])).
% 0.96/1.04  
% 0.96/1.04  fof(f2,axiom,(
% 0.96/1.04    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.96/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.04  
% 0.96/1.04  fof(f36,plain,(
% 0.96/1.04    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.96/1.04    inference(cnf_transformation,[],[f2])).
% 0.96/1.04  
% 0.96/1.04  fof(f3,axiom,(
% 0.96/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.96/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.04  
% 0.96/1.04  fof(f12,plain,(
% 0.96/1.04    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.96/1.04    inference(unused_predicate_definition_removal,[],[f3])).
% 0.96/1.04  
% 0.96/1.04  fof(f13,plain,(
% 0.96/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.96/1.04    inference(ennf_transformation,[],[f12])).
% 0.96/1.04  
% 0.96/1.04  fof(f37,plain,(
% 0.96/1.04    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.96/1.04    inference(cnf_transformation,[],[f13])).
% 0.96/1.04  
% 0.96/1.04  fof(f1,axiom,(
% 0.96/1.04    v1_xboole_0(k1_xboole_0)),
% 0.96/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.04  
% 0.96/1.04  fof(f35,plain,(
% 0.96/1.04    v1_xboole_0(k1_xboole_0)),
% 0.96/1.04    inference(cnf_transformation,[],[f1])).
% 0.96/1.04  
% 0.96/1.04  fof(f4,axiom,(
% 0.96/1.04    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.96/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.04  
% 0.96/1.04  fof(f14,plain,(
% 0.96/1.04    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.96/1.04    inference(ennf_transformation,[],[f4])).
% 0.96/1.04  
% 0.96/1.04  fof(f38,plain,(
% 0.96/1.04    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.96/1.04    inference(cnf_transformation,[],[f14])).
% 0.96/1.04  
% 0.96/1.04  fof(f7,axiom,(
% 0.96/1.04    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 0.96/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.04  
% 0.96/1.04  fof(f19,plain,(
% 0.96/1.04    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.96/1.04    inference(ennf_transformation,[],[f7])).
% 0.96/1.04  
% 0.96/1.04  fof(f20,plain,(
% 0.96/1.04    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.96/1.04    inference(flattening,[],[f19])).
% 0.96/1.04  
% 0.96/1.04  fof(f44,plain,(
% 0.96/1.04    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.96/1.04    inference(cnf_transformation,[],[f20])).
% 0.96/1.04  
% 0.96/1.04  cnf(c_8,plain,
% 0.96/1.04      ( m2_orders_2(sK1(X0,X1),X0,X1)
% 0.96/1.04      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 0.96/1.04      | v2_struct_0(X0)
% 0.96/1.04      | ~ v3_orders_2(X0)
% 0.96/1.04      | ~ v4_orders_2(X0)
% 0.96/1.04      | ~ v5_orders_2(X0)
% 0.96/1.04      | ~ l1_orders_2(X0) ),
% 0.96/1.04      inference(cnf_transformation,[],[f43]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_14,negated_conjecture,
% 0.96/1.04      ( m1_orders_1(sK4,k1_orders_1(u1_struct_0(sK3))) ),
% 0.96/1.04      inference(cnf_transformation,[],[f53]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_249,plain,
% 0.96/1.04      ( m2_orders_2(sK1(X0,X1),X0,X1)
% 0.96/1.04      | v2_struct_0(X0)
% 0.96/1.04      | ~ v3_orders_2(X0)
% 0.96/1.04      | ~ v4_orders_2(X0)
% 0.96/1.04      | ~ v5_orders_2(X0)
% 0.96/1.04      | ~ l1_orders_2(X0)
% 0.96/1.04      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
% 0.96/1.04      | sK4 != X1 ),
% 0.96/1.04      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_250,plain,
% 0.96/1.04      ( m2_orders_2(sK1(X0,sK4),X0,sK4)
% 0.96/1.04      | v2_struct_0(X0)
% 0.96/1.04      | ~ v3_orders_2(X0)
% 0.96/1.04      | ~ v4_orders_2(X0)
% 0.96/1.04      | ~ v5_orders_2(X0)
% 0.96/1.04      | ~ l1_orders_2(X0)
% 0.96/1.04      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3)) ),
% 0.96/1.04      inference(unflattening,[status(thm)],[c_249]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_15,negated_conjecture,
% 0.96/1.04      ( l1_orders_2(sK3) ),
% 0.96/1.04      inference(cnf_transformation,[],[f52]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_535,plain,
% 0.96/1.04      ( m2_orders_2(sK1(X0,sK4),X0,sK4)
% 0.96/1.04      | v2_struct_0(X0)
% 0.96/1.04      | ~ v3_orders_2(X0)
% 0.96/1.04      | ~ v4_orders_2(X0)
% 0.96/1.04      | ~ v5_orders_2(X0)
% 0.96/1.04      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK3))
% 0.96/1.04      | sK3 != X0 ),
% 0.96/1.04      inference(resolution_lifted,[status(thm)],[c_250,c_15]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_536,plain,
% 0.96/1.04      ( m2_orders_2(sK1(sK3,sK4),sK3,sK4)
% 0.96/1.04      | v2_struct_0(sK3)
% 0.96/1.04      | ~ v3_orders_2(sK3)
% 0.96/1.04      | ~ v4_orders_2(sK3)
% 0.96/1.04      | ~ v5_orders_2(sK3)
% 0.96/1.04      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 0.96/1.04      inference(unflattening,[status(thm)],[c_535]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_19,negated_conjecture,
% 0.96/1.04      ( ~ v2_struct_0(sK3) ),
% 0.96/1.04      inference(cnf_transformation,[],[f48]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_18,negated_conjecture,
% 0.96/1.04      ( v3_orders_2(sK3) ),
% 0.96/1.04      inference(cnf_transformation,[],[f49]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_17,negated_conjecture,
% 0.96/1.04      ( v4_orders_2(sK3) ),
% 0.96/1.04      inference(cnf_transformation,[],[f50]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_16,negated_conjecture,
% 0.96/1.04      ( v5_orders_2(sK3) ),
% 0.96/1.04      inference(cnf_transformation,[],[f51]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_538,plain,
% 0.96/1.04      ( m2_orders_2(sK1(sK3,sK4),sK3,sK4)
% 0.96/1.04      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 0.96/1.04      inference(global_propositional_subsumption,
% 0.96/1.04                [status(thm)],
% 0.96/1.04                [c_536,c_19,c_18,c_17,c_16]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_981,plain,
% 0.96/1.04      ( m2_orders_2(sK1(sK3,sK4),sK3,sK4) ),
% 0.96/1.04      inference(equality_resolution_simp,[status(thm)],[c_538]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_1295,plain,
% 0.96/1.04      ( m2_orders_2(sK1(sK3,sK4),sK3,sK4) = iProver_top ),
% 0.96/1.04      inference(predicate_to_equality,[status(thm)],[c_981]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_12,plain,
% 0.96/1.04      ( ~ r2_hidden(X0,X1)
% 0.96/1.04      | k3_tarski(X1) != k1_xboole_0
% 0.96/1.04      | k1_xboole_0 = X0 ),
% 0.96/1.04      inference(cnf_transformation,[],[f45]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_6,plain,
% 0.96/1.04      ( ~ m2_orders_2(X0,X1,X2)
% 0.96/1.04      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 0.96/1.04      | r2_hidden(X0,k4_orders_2(X1,X2))
% 0.96/1.04      | v2_struct_0(X1)
% 0.96/1.04      | ~ v3_orders_2(X1)
% 0.96/1.04      | ~ v4_orders_2(X1)
% 0.96/1.04      | ~ v5_orders_2(X1)
% 0.96/1.04      | ~ l1_orders_2(X1) ),
% 0.96/1.04      inference(cnf_transformation,[],[f55]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_402,plain,
% 0.96/1.04      ( ~ m2_orders_2(X0,X1,X2)
% 0.96/1.04      | r2_hidden(X0,k4_orders_2(X1,X2))
% 0.96/1.04      | v2_struct_0(X1)
% 0.96/1.04      | ~ v3_orders_2(X1)
% 0.96/1.04      | ~ v4_orders_2(X1)
% 0.96/1.04      | ~ v5_orders_2(X1)
% 0.96/1.04      | ~ l1_orders_2(X1)
% 0.96/1.04      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
% 0.96/1.04      | sK4 != X2 ),
% 0.96/1.04      inference(resolution_lifted,[status(thm)],[c_6,c_14]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_403,plain,
% 0.96/1.04      ( ~ m2_orders_2(X0,X1,sK4)
% 0.96/1.04      | r2_hidden(X0,k4_orders_2(X1,sK4))
% 0.96/1.04      | v2_struct_0(X1)
% 0.96/1.04      | ~ v3_orders_2(X1)
% 0.96/1.04      | ~ v4_orders_2(X1)
% 0.96/1.04      | ~ v5_orders_2(X1)
% 0.96/1.04      | ~ l1_orders_2(X1)
% 0.96/1.04      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3)) ),
% 0.96/1.04      inference(unflattening,[status(thm)],[c_402]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_549,plain,
% 0.96/1.04      ( ~ m2_orders_2(X0,X1,sK4)
% 0.96/1.04      | r2_hidden(X0,k4_orders_2(X1,sK4))
% 0.96/1.04      | v2_struct_0(X1)
% 0.96/1.04      | ~ v3_orders_2(X1)
% 0.96/1.04      | ~ v4_orders_2(X1)
% 0.96/1.04      | ~ v5_orders_2(X1)
% 0.96/1.04      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
% 0.96/1.04      | sK3 != X1 ),
% 0.96/1.04      inference(resolution_lifted,[status(thm)],[c_403,c_15]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_550,plain,
% 0.96/1.04      ( ~ m2_orders_2(X0,sK3,sK4)
% 0.96/1.04      | r2_hidden(X0,k4_orders_2(sK3,sK4))
% 0.96/1.04      | v2_struct_0(sK3)
% 0.96/1.04      | ~ v3_orders_2(sK3)
% 0.96/1.04      | ~ v4_orders_2(sK3)
% 0.96/1.04      | ~ v5_orders_2(sK3)
% 0.96/1.04      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 0.96/1.04      inference(unflattening,[status(thm)],[c_549]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_554,plain,
% 0.96/1.04      ( ~ m2_orders_2(X0,sK3,sK4)
% 0.96/1.04      | r2_hidden(X0,k4_orders_2(sK3,sK4))
% 0.96/1.04      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 0.96/1.04      inference(global_propositional_subsumption,
% 0.96/1.04                [status(thm)],
% 0.96/1.04                [c_550,c_19,c_18,c_17,c_16]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_777,plain,
% 0.96/1.04      ( ~ m2_orders_2(X0,sK3,sK4)
% 0.96/1.04      | X0 != X1
% 0.96/1.04      | k4_orders_2(sK3,sK4) != X2
% 0.96/1.04      | k3_tarski(X2) != k1_xboole_0
% 0.96/1.04      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3))
% 0.96/1.04      | k1_xboole_0 = X1 ),
% 0.96/1.04      inference(resolution_lifted,[status(thm)],[c_12,c_554]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_778,plain,
% 0.96/1.04      ( ~ m2_orders_2(X0,sK3,sK4)
% 0.96/1.04      | k3_tarski(k4_orders_2(sK3,sK4)) != k1_xboole_0
% 0.96/1.04      | k1_xboole_0 = X0 ),
% 0.96/1.04      inference(unflattening,[status(thm)],[c_777]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_1307,plain,
% 0.96/1.04      ( k3_tarski(k4_orders_2(sK3,sK4)) != k1_xboole_0
% 0.96/1.04      | k1_xboole_0 = X0
% 0.96/1.04      | m2_orders_2(X0,sK3,sK4) != iProver_top ),
% 0.96/1.04      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_13,negated_conjecture,
% 0.96/1.04      ( k1_xboole_0 = k3_tarski(k4_orders_2(sK3,sK4)) ),
% 0.96/1.04      inference(cnf_transformation,[],[f54]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_1350,plain,
% 0.96/1.04      ( k1_xboole_0 = X0
% 0.96/1.04      | k1_xboole_0 != k1_xboole_0
% 0.96/1.04      | m2_orders_2(X0,sK3,sK4) != iProver_top ),
% 0.96/1.04      inference(light_normalisation,[status(thm)],[c_1307,c_13]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_1351,plain,
% 0.96/1.04      ( k1_xboole_0 = X0 | m2_orders_2(X0,sK3,sK4) != iProver_top ),
% 0.96/1.04      inference(equality_resolution_simp,[status(thm)],[c_1350]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_1423,plain,
% 0.96/1.04      ( sK1(sK3,sK4) = k1_xboole_0 ),
% 0.96/1.04      inference(superposition,[status(thm)],[c_1295,c_1351]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_1425,plain,
% 0.96/1.04      ( m2_orders_2(k1_xboole_0,sK3,sK4) = iProver_top ),
% 0.96/1.04      inference(demodulation,[status(thm)],[c_1423,c_1295]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_1047,plain,( X0 = X0 ),theory(equality) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_1068,plain,
% 0.96/1.04      ( k1_xboole_0 = k1_xboole_0 ),
% 0.96/1.04      inference(instantiation,[status(thm)],[c_1047]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_1049,plain,
% 0.96/1.04      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 0.96/1.04      theory(equality) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_1058,plain,
% 0.96/1.04      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 0.96/1.04      | k1_xboole_0 != k1_xboole_0 ),
% 0.96/1.04      inference(instantiation,[status(thm)],[c_1049]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_1,plain,
% 0.96/1.04      ( r1_tarski(k1_xboole_0,X0) ),
% 0.96/1.04      inference(cnf_transformation,[],[f36]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_2,plain,
% 0.96/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 0.96/1.04      inference(cnf_transformation,[],[f37]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_208,plain,
% 0.96/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | X1 != X2 | k1_xboole_0 != X0 ),
% 0.96/1.04      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_209,plain,
% 0.96/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 0.96/1.04      inference(unflattening,[status(thm)],[c_208]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_0,plain,
% 0.96/1.04      ( v1_xboole_0(k1_xboole_0) ),
% 0.96/1.04      inference(cnf_transformation,[],[f35]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_3,plain,
% 0.96/1.04      ( ~ r2_hidden(X0,X1)
% 0.96/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 0.96/1.04      | ~ v1_xboole_0(X2) ),
% 0.96/1.04      inference(cnf_transformation,[],[f38]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_219,plain,
% 0.96/1.04      ( ~ r2_hidden(X0,X1)
% 0.96/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 0.96/1.04      | k1_xboole_0 != X2 ),
% 0.96/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_220,plain,
% 0.96/1.04      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
% 0.96/1.04      inference(unflattening,[status(thm)],[c_219]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_234,plain,
% 0.96/1.04      ( ~ r2_hidden(X0,X1)
% 0.96/1.04      | k1_zfmisc_1(X2) != k1_zfmisc_1(k1_xboole_0)
% 0.96/1.04      | k1_xboole_0 != X1 ),
% 0.96/1.04      inference(resolution_lifted,[status(thm)],[c_209,c_220]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_235,plain,
% 0.96/1.04      ( ~ r2_hidden(X0,k1_xboole_0)
% 0.96/1.04      | k1_zfmisc_1(X1) != k1_zfmisc_1(k1_xboole_0) ),
% 0.96/1.04      inference(unflattening,[status(thm)],[c_234]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_9,plain,
% 0.96/1.04      ( ~ m2_orders_2(X0,X1,X2)
% 0.96/1.04      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 0.96/1.04      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 0.96/1.04      | v2_struct_0(X1)
% 0.96/1.04      | ~ v3_orders_2(X1)
% 0.96/1.04      | ~ v4_orders_2(X1)
% 0.96/1.04      | ~ v5_orders_2(X1)
% 0.96/1.04      | ~ l1_orders_2(X1) ),
% 0.96/1.04      inference(cnf_transformation,[],[f44]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_342,plain,
% 0.96/1.04      ( ~ m2_orders_2(X0,X1,X2)
% 0.96/1.04      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 0.96/1.04      | v2_struct_0(X1)
% 0.96/1.04      | ~ v3_orders_2(X1)
% 0.96/1.04      | ~ v4_orders_2(X1)
% 0.96/1.04      | ~ v5_orders_2(X1)
% 0.96/1.04      | ~ l1_orders_2(X1)
% 0.96/1.04      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
% 0.96/1.04      | sK4 != X2 ),
% 0.96/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 0.96/1.04  
% 0.96/1.04  cnf(c_343,plain,
% 0.96/1.04      ( ~ m2_orders_2(X0,X1,sK4)
% 0.96/1.04      | r2_hidden(k1_funct_1(sK4,u1_struct_0(X1)),X0)
% 0.96/1.04      | v2_struct_0(X1)
% 0.96/1.04      | ~ v3_orders_2(X1)
% 0.96/1.04      | ~ v4_orders_2(X1)
% 0.96/1.04      | ~ v5_orders_2(X1)
% 0.96/1.05      | ~ l1_orders_2(X1)
% 0.96/1.05      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3)) ),
% 0.96/1.05      inference(unflattening,[status(thm)],[c_342]) ).
% 0.96/1.05  
% 0.96/1.05  cnf(c_591,plain,
% 0.96/1.05      ( ~ m2_orders_2(X0,X1,sK4)
% 0.96/1.05      | r2_hidden(k1_funct_1(sK4,u1_struct_0(X1)),X0)
% 0.96/1.05      | v2_struct_0(X1)
% 0.96/1.05      | ~ v3_orders_2(X1)
% 0.96/1.05      | ~ v4_orders_2(X1)
% 0.96/1.05      | ~ v5_orders_2(X1)
% 0.96/1.05      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK3))
% 0.96/1.05      | sK3 != X1 ),
% 0.96/1.05      inference(resolution_lifted,[status(thm)],[c_343,c_15]) ).
% 0.96/1.05  
% 0.96/1.05  cnf(c_592,plain,
% 0.96/1.05      ( ~ m2_orders_2(X0,sK3,sK4)
% 0.96/1.05      | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X0)
% 0.96/1.05      | v2_struct_0(sK3)
% 0.96/1.05      | ~ v3_orders_2(sK3)
% 0.96/1.05      | ~ v4_orders_2(sK3)
% 0.96/1.05      | ~ v5_orders_2(sK3)
% 0.96/1.05      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 0.96/1.05      inference(unflattening,[status(thm)],[c_591]) ).
% 0.96/1.05  
% 0.96/1.05  cnf(c_596,plain,
% 0.96/1.05      ( ~ m2_orders_2(X0,sK3,sK4)
% 0.96/1.05      | r2_hidden(k1_funct_1(sK4,u1_struct_0(sK3)),X0)
% 0.96/1.05      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3)) ),
% 0.96/1.05      inference(global_propositional_subsumption,
% 0.96/1.05                [status(thm)],
% 0.96/1.05                [c_592,c_19,c_18,c_17,c_16]) ).
% 0.96/1.05  
% 0.96/1.05  cnf(c_874,plain,
% 0.96/1.05      ( ~ m2_orders_2(X0,sK3,sK4)
% 0.96/1.05      | k1_funct_1(sK4,u1_struct_0(sK3)) != X1
% 0.96/1.05      | k1_orders_1(u1_struct_0(sK3)) != k1_orders_1(u1_struct_0(sK3))
% 0.96/1.05      | k1_zfmisc_1(X2) != k1_zfmisc_1(k1_xboole_0)
% 0.96/1.05      | k1_xboole_0 != X0 ),
% 0.96/1.05      inference(resolution_lifted,[status(thm)],[c_235,c_596]) ).
% 0.96/1.05  
% 0.96/1.05  cnf(c_875,plain,
% 0.96/1.05      ( ~ m2_orders_2(k1_xboole_0,sK3,sK4)
% 0.96/1.05      | k1_zfmisc_1(X0) != k1_zfmisc_1(k1_xboole_0) ),
% 0.96/1.05      inference(unflattening,[status(thm)],[c_874]) ).
% 0.96/1.05  
% 0.96/1.05  cnf(c_876,plain,
% 0.96/1.05      ( k1_zfmisc_1(X0) != k1_zfmisc_1(k1_xboole_0)
% 0.96/1.05      | m2_orders_2(k1_xboole_0,sK3,sK4) != iProver_top ),
% 0.96/1.05      inference(predicate_to_equality,[status(thm)],[c_875]) ).
% 0.96/1.05  
% 0.96/1.05  cnf(c_878,plain,
% 0.96/1.05      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 0.96/1.05      | m2_orders_2(k1_xboole_0,sK3,sK4) != iProver_top ),
% 0.96/1.05      inference(instantiation,[status(thm)],[c_876]) ).
% 0.96/1.05  
% 0.96/1.05  cnf(contradiction,plain,
% 0.96/1.05      ( $false ),
% 0.96/1.05      inference(minisat,[status(thm)],[c_1425,c_1068,c_1058,c_878]) ).
% 0.96/1.05  
% 0.96/1.05  
% 0.96/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 0.96/1.05  
% 0.96/1.05  ------                               Statistics
% 0.96/1.05  
% 0.96/1.05  ------ General
% 0.96/1.05  
% 0.96/1.05  abstr_ref_over_cycles:                  0
% 0.96/1.05  abstr_ref_under_cycles:                 0
% 0.96/1.05  gc_basic_clause_elim:                   0
% 0.96/1.05  forced_gc_time:                         0
% 0.96/1.05  parsing_time:                           0.016
% 0.96/1.05  unif_index_cands_time:                  0.
% 0.96/1.05  unif_index_add_time:                    0.
% 0.96/1.05  orderings_time:                         0.
% 0.96/1.05  out_proof_time:                         0.007
% 0.96/1.05  total_time:                             0.062
% 0.96/1.05  num_of_symbols:                         56
% 0.96/1.05  num_of_terms:                           789
% 0.96/1.05  
% 0.96/1.05  ------ Preprocessing
% 0.96/1.05  
% 0.96/1.05  num_of_splits:                          3
% 0.96/1.05  num_of_split_atoms:                     2
% 0.96/1.05  num_of_reused_defs:                     1
% 0.96/1.05  num_eq_ax_congr_red:                    12
% 0.96/1.05  num_of_sem_filtered_clauses:            2
% 0.96/1.05  num_of_subtypes:                        0
% 0.96/1.05  monotx_restored_types:                  0
% 0.96/1.05  sat_num_of_epr_types:                   0
% 0.96/1.05  sat_num_of_non_cyclic_types:            0
% 0.96/1.05  sat_guarded_non_collapsed_types:        0
% 0.96/1.05  num_pure_diseq_elim:                    0
% 0.96/1.05  simp_replaced_by:                       0
% 0.96/1.05  res_preprocessed:                       88
% 0.96/1.05  prep_upred:                             0
% 0.96/1.05  prep_unflattend:                        46
% 0.96/1.05  smt_new_axioms:                         0
% 0.96/1.05  pred_elim_cands:                        1
% 0.96/1.05  pred_elim:                              10
% 0.96/1.05  pred_elim_cl:                           6
% 0.96/1.05  pred_elim_cycles:                       13
% 0.96/1.05  merged_defs:                            0
% 0.96/1.05  merged_defs_ncl:                        0
% 0.96/1.05  bin_hyper_res:                          0
% 0.96/1.05  prep_cycles:                            4
% 0.96/1.05  pred_elim_time:                         0.01
% 0.96/1.05  splitting_time:                         0.
% 0.96/1.05  sem_filter_time:                        0.
% 0.96/1.05  monotx_time:                            0.
% 0.96/1.05  subtype_inf_time:                       0.
% 0.96/1.05  
% 0.96/1.05  ------ Problem properties
% 0.96/1.05  
% 0.96/1.05  clauses:                                17
% 0.96/1.05  conjectures:                            1
% 0.96/1.05  epr:                                    1
% 0.96/1.05  horn:                                   12
% 0.96/1.05  ground:                                 6
% 0.96/1.05  unary:                                  2
% 0.96/1.05  binary:                                 8
% 0.96/1.05  lits:                                   42
% 0.96/1.05  lits_eq:                                23
% 0.96/1.05  fd_pure:                                0
% 0.96/1.05  fd_pseudo:                              0
% 0.96/1.05  fd_cond:                                4
% 0.96/1.05  fd_pseudo_cond:                         0
% 0.96/1.05  ac_symbols:                             0
% 0.96/1.05  
% 0.96/1.05  ------ Propositional Solver
% 0.96/1.05  
% 0.96/1.05  prop_solver_calls:                      22
% 0.96/1.05  prop_fast_solver_calls:                 660
% 0.96/1.05  smt_solver_calls:                       0
% 0.96/1.05  smt_fast_solver_calls:                  0
% 0.96/1.05  prop_num_of_clauses:                    258
% 0.96/1.05  prop_preprocess_simplified:             2027
% 0.96/1.05  prop_fo_subsumed:                       30
% 0.96/1.05  prop_solver_time:                       0.
% 0.96/1.05  smt_solver_time:                        0.
% 0.96/1.05  smt_fast_solver_time:                   0.
% 0.96/1.05  prop_fast_solver_time:                  0.
% 0.96/1.05  prop_unsat_core_time:                   0.
% 0.96/1.05  
% 0.96/1.05  ------ QBF
% 0.96/1.05  
% 0.96/1.05  qbf_q_res:                              0
% 0.96/1.05  qbf_num_tautologies:                    0
% 0.96/1.05  qbf_prep_cycles:                        0
% 0.96/1.05  
% 0.96/1.05  ------ BMC1
% 0.96/1.05  
% 0.96/1.05  bmc1_current_bound:                     -1
% 0.96/1.05  bmc1_last_solved_bound:                 -1
% 0.96/1.05  bmc1_unsat_core_size:                   -1
% 0.96/1.05  bmc1_unsat_core_parents_size:           -1
% 0.96/1.05  bmc1_merge_next_fun:                    0
% 0.96/1.05  bmc1_unsat_core_clauses_time:           0.
% 0.96/1.05  
% 0.96/1.05  ------ Instantiation
% 0.96/1.05  
% 0.96/1.05  inst_num_of_clauses:                    28
% 0.96/1.05  inst_num_in_passive:                    6
% 0.96/1.05  inst_num_in_active:                     20
% 0.96/1.05  inst_num_in_unprocessed:                2
% 0.96/1.05  inst_num_of_loops:                      20
% 0.96/1.05  inst_num_of_learning_restarts:          0
% 0.96/1.05  inst_num_moves_active_passive:          0
% 0.96/1.05  inst_lit_activity:                      0
% 0.96/1.05  inst_lit_activity_moves:                0
% 0.96/1.05  inst_num_tautologies:                   0
% 0.96/1.05  inst_num_prop_implied:                  0
% 0.96/1.05  inst_num_existing_simplified:           0
% 0.96/1.05  inst_num_eq_res_simplified:             0
% 0.96/1.05  inst_num_child_elim:                    0
% 0.96/1.05  inst_num_of_dismatching_blockings:      0
% 0.96/1.05  inst_num_of_non_proper_insts:           2
% 0.96/1.05  inst_num_of_duplicates:                 0
% 0.96/1.05  inst_inst_num_from_inst_to_res:         0
% 0.96/1.05  inst_dismatching_checking_time:         0.
% 0.96/1.05  
% 0.96/1.05  ------ Resolution
% 0.96/1.05  
% 0.96/1.05  res_num_of_clauses:                     0
% 0.96/1.05  res_num_in_passive:                     0
% 0.96/1.05  res_num_in_active:                      0
% 0.96/1.05  res_num_of_loops:                       92
% 0.96/1.05  res_forward_subset_subsumed:            0
% 0.96/1.05  res_backward_subset_subsumed:           0
% 0.96/1.05  res_forward_subsumed:                   0
% 0.96/1.05  res_backward_subsumed:                  0
% 0.96/1.05  res_forward_subsumption_resolution:     0
% 0.96/1.05  res_backward_subsumption_resolution:    0
% 0.96/1.05  res_clause_to_clause_subsumption:       37
% 0.96/1.05  res_orphan_elimination:                 0
% 0.96/1.05  res_tautology_del:                      7
% 0.96/1.05  res_num_eq_res_simplified:              1
% 0.96/1.05  res_num_sel_changes:                    0
% 0.96/1.05  res_moves_from_active_to_pass:          0
% 0.96/1.05  
% 0.96/1.05  ------ Superposition
% 0.96/1.05  
% 0.96/1.05  sup_time_total:                         0.
% 0.96/1.05  sup_time_generating:                    0.
% 0.96/1.05  sup_time_sim_full:                      0.
% 0.96/1.05  sup_time_sim_immed:                     0.
% 0.96/1.05  
% 0.96/1.05  sup_num_of_clauses:                     16
% 0.96/1.05  sup_num_in_active:                      2
% 0.96/1.05  sup_num_in_passive:                     14
% 0.96/1.05  sup_num_of_loops:                       3
% 0.96/1.05  sup_fw_superposition:                   0
% 0.96/1.05  sup_bw_superposition:                   1
% 0.96/1.05  sup_immediate_simplified:               0
% 0.96/1.05  sup_given_eliminated:                   0
% 0.96/1.05  comparisons_done:                       0
% 0.96/1.05  comparisons_avoided:                    0
% 0.96/1.05  
% 0.96/1.05  ------ Simplifications
% 0.96/1.05  
% 0.96/1.05  
% 0.96/1.05  sim_fw_subset_subsumed:                 0
% 0.96/1.05  sim_bw_subset_subsumed:                 0
% 0.96/1.05  sim_fw_subsumed:                        0
% 0.96/1.05  sim_bw_subsumed:                        0
% 0.96/1.05  sim_fw_subsumption_res:                 1
% 0.96/1.05  sim_bw_subsumption_res:                 0
% 0.96/1.05  sim_tautology_del:                      0
% 0.96/1.05  sim_eq_tautology_del:                   1
% 0.96/1.05  sim_eq_res_simp:                        1
% 0.96/1.05  sim_fw_demodulated:                     1
% 0.96/1.05  sim_bw_demodulated:                     1
% 0.96/1.05  sim_light_normalised:                   1
% 0.96/1.05  sim_joinable_taut:                      0
% 0.96/1.05  sim_joinable_simp:                      0
% 0.96/1.05  sim_ac_normalised:                      0
% 0.96/1.05  sim_smt_subsumption:                    0
% 0.96/1.05  
%------------------------------------------------------------------------------
