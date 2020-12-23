%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1178+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:05 EST 2020

% Result     : Theorem 1.22s
% Output     : CNFRefutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 194 expanded)
%              Number of clauses        :   37 (  52 expanded)
%              Number of leaves         :   11 (  52 expanded)
%              Depth                    :   21
%              Number of atoms          :  351 (1030 expanded)
%              Number of equality atoms :   85 ( 207 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => m2_orders_2(k1_tarski(k1_funct_1(X1,u1_struct_0(X0))),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m2_orders_2(k1_tarski(k1_funct_1(X1,u1_struct_0(X0))),X0,X1)
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m2_orders_2(k1_tarski(k1_funct_1(X1,u1_struct_0(X0))),X0,X1)
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m2_orders_2(k1_tarski(k1_funct_1(X1,u1_struct_0(X0))),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK3))
        & m1_orders_1(sK3,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
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
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2))) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3))
    & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f25,f24])).

fof(f43,plain,(
    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
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

fof(f9,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f6])).

fof(f15,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK1(X0),X0)
        & k1_xboole_0 != sK1(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK1(X0),X0)
          & k1_xboole_0 != sK1(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f22])).

fof(f35,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f28,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m2_orders_2(X4,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_7,plain,
    ( m2_orders_2(k1_tarski(k1_funct_1(X0,u1_struct_0(X1))),X1,X0)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_12,negated_conjecture,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_323,plain,
    ( m2_orders_2(k1_tarski(k1_funct_1(X0,u1_struct_0(X1))),X1,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_324,plain,
    ( m2_orders_2(k1_tarski(k1_funct_1(sK3,u1_struct_0(X0))),X0,sK3)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_13,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_396,plain,
    ( m2_orders_2(k1_tarski(k1_funct_1(sK3,u1_struct_0(X0))),X0,sK3)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_324,c_13])).

cnf(c_397,plain,
    ( m2_orders_2(k1_tarski(k1_funct_1(sK3,u1_struct_0(sK2))),sK2,sK3)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_16,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_399,plain,
    ( m2_orders_2(k1_tarski(k1_funct_1(sK3,u1_struct_0(sK2))),sK2,sK3)
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_17,c_16,c_15,c_14])).

cnf(c_787,plain,
    ( m2_orders_2(k1_tarski(k1_funct_1(sK3,u1_struct_0(sK2))),sK2,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_399])).

cnf(c_1017,plain,
    ( m2_orders_2(k1_tarski(k1_funct_1(sK3,u1_struct_0(sK2))),sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_293,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_294,plain,
    ( ~ m2_orders_2(X0,X1,sK3)
    | r2_hidden(X0,k4_orders_2(X1,sK3))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_458,plain,
    ( ~ m2_orders_2(X0,X1,sK3)
    | r2_hidden(X0,k4_orders_2(X1,sK3))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_294,c_13])).

cnf(c_459,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | r2_hidden(X0,k4_orders_2(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_463,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | r2_hidden(X0,k4_orders_2(sK2,sK3))
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_17,c_16,c_15,c_14])).

cnf(c_646,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | X0 != X1
    | k4_orders_2(sK2,sK3) != X2
    | k3_tarski(X2) != k1_xboole_0
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2))
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_463])).

cnf(c_647,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | k3_tarski(k4_orders_2(sK2,sK3)) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_1018,plain,
    ( k3_tarski(k4_orders_2(sK2,sK3)) != k1_xboole_0
    | k1_xboole_0 = X0
    | m2_orders_2(X0,sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_4,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_190,plain,
    ( k1_xboole_0 = X0
    | o_0_0_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_6])).

cnf(c_191,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1026,plain,
    ( k3_tarski(k4_orders_2(sK2,sK3)) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11,c_191])).

cnf(c_1037,plain,
    ( k1_xboole_0 = X0
    | o_0_0_xboole_0 != o_0_0_xboole_0
    | m2_orders_2(X0,sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1018,c_191,c_1026])).

cnf(c_1038,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK2,sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1037])).

cnf(c_1039,plain,
    ( o_0_0_xboole_0 = X0
    | m2_orders_2(X0,sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1038,c_191])).

cnf(c_1097,plain,
    ( k1_tarski(k1_funct_1(sK3,u1_struct_0(sK2))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1017,c_1039])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_185,plain,
    ( k1_tarski(X0) != o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_1287,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1097,c_185])).


%------------------------------------------------------------------------------
