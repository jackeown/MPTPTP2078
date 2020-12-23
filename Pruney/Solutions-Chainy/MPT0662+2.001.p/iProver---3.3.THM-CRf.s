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
% DateTime   : Thu Dec  3 11:50:57 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 198 expanded)
%              Number of clauses        :   48 (  71 expanded)
%              Number of leaves         :   12 (  38 expanded)
%              Depth                    :   18
%              Number of atoms          :  330 ( 713 expanded)
%              Number of equality atoms :  144 ( 225 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK4,sK2) != k1_funct_1(k7_relat_1(sK4,sK3),sK2)
      & r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3)))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k7_relat_1(sK4,sK3),sK2)
    & r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3)))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f28])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK0(X0,X1) != sK1(X0,X1)
          | ~ r2_hidden(sK0(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( ( sK0(X0,X1) = sK1(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK0(X0,X1) != sK1(X0,X1)
              | ~ r2_hidden(sK0(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( ( sK0(X0,X1) = sK1(X0,X1)
                & r2_hidden(sK0(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f31,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X4,X0,X5] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    k1_funct_1(sK4,sK2) != k1_funct_1(k7_relat_1(sK4,sK3),sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_492,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_493,plain,
    ( r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_501,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1051,plain,
    ( r2_hidden(sK2,sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_493,c_501])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_24,plain,
    ( r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_712,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3)))
    | r2_hidden(sK2,sK3)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_713,plain,
    ( r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3))) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_2755,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1051,c_22,c_24,c_713])).

cnf(c_7,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_497,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1509,plain,
    ( k1_funct_1(X0,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X0),X2)
    | r2_hidden(X2,X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k6_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_497])).

cnf(c_13,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_498,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_499,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1986,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2))
    | r2_hidden(X2,X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1509,c_498,c_499])).

cnf(c_2760,plain,
    ( k1_funct_1(X0,k1_funct_1(k6_relat_1(sK3),sK2)) = k1_funct_1(k5_relat_1(k6_relat_1(sK3),X0),sK2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2755,c_1986])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_496,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
    | ~ v1_relat_1(k6_relat_1(X2))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_505,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2)) != iProver_top
    | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_533,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X1,X0),k6_relat_1(X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_505,c_498])).

cnf(c_2140,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,k1_relat_1(k6_relat_1(X0))) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_496,c_533])).

cnf(c_2145,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2140,c_7])).

cnf(c_37,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_40,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2171,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2145,c_37,c_40])).

cnf(c_2761,plain,
    ( k1_funct_1(k6_relat_1(sK3),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_2755,c_2171])).

cnf(c_2764,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK3),X0),sK2) = k1_funct_1(X0,sK2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2760,c_2761])).

cnf(c_29899,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) = k1_funct_1(sK4,sK2)
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_492,c_2764])).

cnf(c_491,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_500,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1040,plain,
    ( k5_relat_1(k6_relat_1(X0),sK4) = k7_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_491,c_500])).

cnf(c_29902,plain,
    ( k1_funct_1(k7_relat_1(sK4,sK3),sK2) = k1_funct_1(sK4,sK2)
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29899,c_1040])).

cnf(c_184,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_848,plain,
    ( k1_funct_1(sK4,sK2) = k1_funct_1(sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_185,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_715,plain,
    ( k1_funct_1(k7_relat_1(sK4,sK3),sK2) != X0
    | k1_funct_1(sK4,sK2) != X0
    | k1_funct_1(sK4,sK2) = k1_funct_1(k7_relat_1(sK4,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_847,plain,
    ( k1_funct_1(k7_relat_1(sK4,sK3),sK2) != k1_funct_1(sK4,sK2)
    | k1_funct_1(sK4,sK2) = k1_funct_1(k7_relat_1(sK4,sK3),sK2)
    | k1_funct_1(sK4,sK2) != k1_funct_1(sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_18,negated_conjecture,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k7_relat_1(sK4,sK3),sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29902,c_848,c_847,c_18,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:36:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.67/1.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/1.53  
% 7.67/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.67/1.53  
% 7.67/1.53  ------  iProver source info
% 7.67/1.53  
% 7.67/1.53  git: date: 2020-06-30 10:37:57 +0100
% 7.67/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.67/1.53  git: non_committed_changes: false
% 7.67/1.53  git: last_make_outside_of_git: false
% 7.67/1.53  
% 7.67/1.53  ------ 
% 7.67/1.53  
% 7.67/1.53  ------ Input Options
% 7.67/1.53  
% 7.67/1.53  --out_options                           all
% 7.67/1.53  --tptp_safe_out                         true
% 7.67/1.53  --problem_path                          ""
% 7.67/1.53  --include_path                          ""
% 7.67/1.53  --clausifier                            res/vclausify_rel
% 7.67/1.53  --clausifier_options                    --mode clausify
% 7.67/1.53  --stdin                                 false
% 7.67/1.53  --stats_out                             sel
% 7.67/1.53  
% 7.67/1.53  ------ General Options
% 7.67/1.53  
% 7.67/1.53  --fof                                   false
% 7.67/1.53  --time_out_real                         604.99
% 7.67/1.53  --time_out_virtual                      -1.
% 7.67/1.53  --symbol_type_check                     false
% 7.67/1.53  --clausify_out                          false
% 7.67/1.53  --sig_cnt_out                           false
% 7.67/1.53  --trig_cnt_out                          false
% 7.67/1.53  --trig_cnt_out_tolerance                1.
% 7.67/1.53  --trig_cnt_out_sk_spl                   false
% 7.67/1.53  --abstr_cl_out                          false
% 7.67/1.53  
% 7.67/1.53  ------ Global Options
% 7.67/1.53  
% 7.67/1.53  --schedule                              none
% 7.67/1.53  --add_important_lit                     false
% 7.67/1.53  --prop_solver_per_cl                    1000
% 7.67/1.53  --min_unsat_core                        false
% 7.67/1.53  --soft_assumptions                      false
% 7.67/1.53  --soft_lemma_size                       3
% 7.67/1.53  --prop_impl_unit_size                   0
% 7.67/1.53  --prop_impl_unit                        []
% 7.67/1.53  --share_sel_clauses                     true
% 7.67/1.53  --reset_solvers                         false
% 7.67/1.53  --bc_imp_inh                            [conj_cone]
% 7.67/1.53  --conj_cone_tolerance                   3.
% 7.67/1.53  --extra_neg_conj                        none
% 7.67/1.53  --large_theory_mode                     true
% 7.67/1.53  --prolific_symb_bound                   200
% 7.67/1.53  --lt_threshold                          2000
% 7.67/1.53  --clause_weak_htbl                      true
% 7.67/1.53  --gc_record_bc_elim                     false
% 7.67/1.53  
% 7.67/1.53  ------ Preprocessing Options
% 7.67/1.53  
% 7.67/1.53  --preprocessing_flag                    true
% 7.67/1.53  --time_out_prep_mult                    0.1
% 7.67/1.53  --splitting_mode                        input
% 7.67/1.53  --splitting_grd                         true
% 7.67/1.53  --splitting_cvd                         false
% 7.67/1.53  --splitting_cvd_svl                     false
% 7.67/1.53  --splitting_nvd                         32
% 7.67/1.53  --sub_typing                            true
% 7.67/1.53  --prep_gs_sim                           false
% 7.67/1.53  --prep_unflatten                        true
% 7.67/1.53  --prep_res_sim                          true
% 7.67/1.53  --prep_upred                            true
% 7.67/1.53  --prep_sem_filter                       exhaustive
% 7.67/1.53  --prep_sem_filter_out                   false
% 7.67/1.53  --pred_elim                             false
% 7.67/1.53  --res_sim_input                         true
% 7.67/1.53  --eq_ax_congr_red                       true
% 7.67/1.53  --pure_diseq_elim                       true
% 7.67/1.53  --brand_transform                       false
% 7.67/1.53  --non_eq_to_eq                          false
% 7.67/1.53  --prep_def_merge                        true
% 7.67/1.53  --prep_def_merge_prop_impl              false
% 7.67/1.53  --prep_def_merge_mbd                    true
% 7.67/1.53  --prep_def_merge_tr_red                 false
% 7.67/1.53  --prep_def_merge_tr_cl                  false
% 7.67/1.53  --smt_preprocessing                     true
% 7.67/1.53  --smt_ac_axioms                         fast
% 7.67/1.53  --preprocessed_out                      false
% 7.67/1.53  --preprocessed_stats                    false
% 7.67/1.53  
% 7.67/1.53  ------ Abstraction refinement Options
% 7.67/1.53  
% 7.67/1.53  --abstr_ref                             []
% 7.67/1.53  --abstr_ref_prep                        false
% 7.67/1.53  --abstr_ref_until_sat                   false
% 7.67/1.53  --abstr_ref_sig_restrict                funpre
% 7.67/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.53  --abstr_ref_under                       []
% 7.67/1.53  
% 7.67/1.53  ------ SAT Options
% 7.67/1.53  
% 7.67/1.53  --sat_mode                              false
% 7.67/1.53  --sat_fm_restart_options                ""
% 7.67/1.53  --sat_gr_def                            false
% 7.67/1.53  --sat_epr_types                         true
% 7.67/1.53  --sat_non_cyclic_types                  false
% 7.67/1.53  --sat_finite_models                     false
% 7.67/1.53  --sat_fm_lemmas                         false
% 7.67/1.53  --sat_fm_prep                           false
% 7.67/1.53  --sat_fm_uc_incr                        true
% 7.67/1.53  --sat_out_model                         small
% 7.67/1.53  --sat_out_clauses                       false
% 7.67/1.53  
% 7.67/1.53  ------ QBF Options
% 7.67/1.53  
% 7.67/1.53  --qbf_mode                              false
% 7.67/1.53  --qbf_elim_univ                         false
% 7.67/1.53  --qbf_dom_inst                          none
% 7.67/1.53  --qbf_dom_pre_inst                      false
% 7.67/1.53  --qbf_sk_in                             false
% 7.67/1.53  --qbf_pred_elim                         true
% 7.67/1.53  --qbf_split                             512
% 7.67/1.53  
% 7.67/1.53  ------ BMC1 Options
% 7.67/1.53  
% 7.67/1.53  --bmc1_incremental                      false
% 7.67/1.53  --bmc1_axioms                           reachable_all
% 7.67/1.53  --bmc1_min_bound                        0
% 7.67/1.53  --bmc1_max_bound                        -1
% 7.67/1.53  --bmc1_max_bound_default                -1
% 7.67/1.53  --bmc1_symbol_reachability              true
% 7.67/1.53  --bmc1_property_lemmas                  false
% 7.67/1.53  --bmc1_k_induction                      false
% 7.67/1.53  --bmc1_non_equiv_states                 false
% 7.67/1.53  --bmc1_deadlock                         false
% 7.67/1.53  --bmc1_ucm                              false
% 7.67/1.53  --bmc1_add_unsat_core                   none
% 7.67/1.53  --bmc1_unsat_core_children              false
% 7.67/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.53  --bmc1_out_stat                         full
% 7.67/1.53  --bmc1_ground_init                      false
% 7.67/1.53  --bmc1_pre_inst_next_state              false
% 7.67/1.53  --bmc1_pre_inst_state                   false
% 7.67/1.53  --bmc1_pre_inst_reach_state             false
% 7.67/1.53  --bmc1_out_unsat_core                   false
% 7.67/1.53  --bmc1_aig_witness_out                  false
% 7.67/1.53  --bmc1_verbose                          false
% 7.67/1.53  --bmc1_dump_clauses_tptp                false
% 7.67/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.53  --bmc1_dump_file                        -
% 7.67/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.53  --bmc1_ucm_extend_mode                  1
% 7.67/1.53  --bmc1_ucm_init_mode                    2
% 7.67/1.53  --bmc1_ucm_cone_mode                    none
% 7.67/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.53  --bmc1_ucm_relax_model                  4
% 7.67/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.53  --bmc1_ucm_layered_model                none
% 7.67/1.53  --bmc1_ucm_max_lemma_size               10
% 7.67/1.53  
% 7.67/1.53  ------ AIG Options
% 7.67/1.53  
% 7.67/1.53  --aig_mode                              false
% 7.67/1.53  
% 7.67/1.53  ------ Instantiation Options
% 7.67/1.53  
% 7.67/1.53  --instantiation_flag                    true
% 7.67/1.53  --inst_sos_flag                         false
% 7.67/1.53  --inst_sos_phase                        true
% 7.67/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.53  --inst_lit_sel_side                     num_symb
% 7.67/1.53  --inst_solver_per_active                1400
% 7.67/1.53  --inst_solver_calls_frac                1.
% 7.67/1.53  --inst_passive_queue_type               priority_queues
% 7.67/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.53  --inst_passive_queues_freq              [25;2]
% 7.67/1.53  --inst_dismatching                      true
% 7.67/1.53  --inst_eager_unprocessed_to_passive     true
% 7.67/1.53  --inst_prop_sim_given                   true
% 7.67/1.53  --inst_prop_sim_new                     false
% 7.67/1.53  --inst_subs_new                         false
% 7.67/1.53  --inst_eq_res_simp                      false
% 7.67/1.53  --inst_subs_given                       false
% 7.67/1.53  --inst_orphan_elimination               true
% 7.67/1.53  --inst_learning_loop_flag               true
% 7.67/1.53  --inst_learning_start                   3000
% 7.67/1.53  --inst_learning_factor                  2
% 7.67/1.53  --inst_start_prop_sim_after_learn       3
% 7.67/1.53  --inst_sel_renew                        solver
% 7.67/1.53  --inst_lit_activity_flag                true
% 7.67/1.53  --inst_restr_to_given                   false
% 7.67/1.53  --inst_activity_threshold               500
% 7.67/1.53  --inst_out_proof                        true
% 7.67/1.53  
% 7.67/1.53  ------ Resolution Options
% 7.67/1.53  
% 7.67/1.53  --resolution_flag                       true
% 7.67/1.53  --res_lit_sel                           adaptive
% 7.67/1.53  --res_lit_sel_side                      none
% 7.67/1.53  --res_ordering                          kbo
% 7.67/1.53  --res_to_prop_solver                    active
% 7.67/1.53  --res_prop_simpl_new                    false
% 7.67/1.53  --res_prop_simpl_given                  true
% 7.67/1.53  --res_passive_queue_type                priority_queues
% 7.67/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.53  --res_passive_queues_freq               [15;5]
% 7.67/1.53  --res_forward_subs                      full
% 7.67/1.53  --res_backward_subs                     full
% 7.67/1.53  --res_forward_subs_resolution           true
% 7.67/1.53  --res_backward_subs_resolution          true
% 7.67/1.53  --res_orphan_elimination                true
% 7.67/1.53  --res_time_limit                        2.
% 7.67/1.53  --res_out_proof                         true
% 7.67/1.53  
% 7.67/1.53  ------ Superposition Options
% 7.67/1.53  
% 7.67/1.53  --superposition_flag                    true
% 7.67/1.53  --sup_passive_queue_type                priority_queues
% 7.67/1.53  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.53  --sup_passive_queues_freq               [1;4]
% 7.67/1.53  --demod_completeness_check              fast
% 7.67/1.53  --demod_use_ground                      true
% 7.67/1.53  --sup_to_prop_solver                    passive
% 7.67/1.53  --sup_prop_simpl_new                    true
% 7.67/1.53  --sup_prop_simpl_given                  true
% 7.67/1.53  --sup_fun_splitting                     false
% 7.67/1.53  --sup_smt_interval                      50000
% 7.67/1.53  
% 7.67/1.53  ------ Superposition Simplification Setup
% 7.67/1.53  
% 7.67/1.53  --sup_indices_passive                   []
% 7.67/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.53  --sup_full_bw                           [BwDemod]
% 7.67/1.53  --sup_immed_triv                        [TrivRules]
% 7.67/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.53  --sup_immed_bw_main                     []
% 7.67/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.67/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.67/1.53  
% 7.67/1.53  ------ Combination Options
% 7.67/1.53  
% 7.67/1.53  --comb_res_mult                         3
% 7.67/1.53  --comb_sup_mult                         2
% 7.67/1.53  --comb_inst_mult                        10
% 7.67/1.53  
% 7.67/1.53  ------ Debug Options
% 7.67/1.53  
% 7.67/1.53  --dbg_backtrace                         false
% 7.67/1.53  --dbg_dump_prop_clauses                 false
% 7.67/1.53  --dbg_dump_prop_clauses_file            -
% 7.67/1.53  --dbg_out_stat                          false
% 7.67/1.53  ------ Parsing...
% 7.67/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.67/1.53  
% 7.67/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.67/1.53  
% 7.67/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.67/1.53  
% 7.67/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.53  ------ Proving...
% 7.67/1.53  ------ Problem Properties 
% 7.67/1.53  
% 7.67/1.53  
% 7.67/1.53  clauses                                 22
% 7.67/1.53  conjectures                             4
% 7.67/1.53  EPR                                     2
% 7.67/1.53  Horn                                    20
% 7.67/1.53  unary                                   8
% 7.67/1.53  binary                                  1
% 7.67/1.53  lits                                    60
% 7.67/1.53  lits eq                                 12
% 7.67/1.53  fd_pure                                 0
% 7.67/1.53  fd_pseudo                               0
% 7.67/1.53  fd_cond                                 0
% 7.67/1.53  fd_pseudo_cond                          5
% 7.67/1.53  AC symbols                              0
% 7.67/1.53  
% 7.67/1.53  ------ Input Options Time Limit: Unbounded
% 7.67/1.53  
% 7.67/1.53  
% 7.67/1.53  ------ 
% 7.67/1.53  Current options:
% 7.67/1.53  ------ 
% 7.67/1.53  
% 7.67/1.53  ------ Input Options
% 7.67/1.53  
% 7.67/1.53  --out_options                           all
% 7.67/1.53  --tptp_safe_out                         true
% 7.67/1.53  --problem_path                          ""
% 7.67/1.53  --include_path                          ""
% 7.67/1.53  --clausifier                            res/vclausify_rel
% 7.67/1.53  --clausifier_options                    --mode clausify
% 7.67/1.53  --stdin                                 false
% 7.67/1.53  --stats_out                             sel
% 7.67/1.53  
% 7.67/1.53  ------ General Options
% 7.67/1.53  
% 7.67/1.53  --fof                                   false
% 7.67/1.53  --time_out_real                         604.99
% 7.67/1.53  --time_out_virtual                      -1.
% 7.67/1.53  --symbol_type_check                     false
% 7.67/1.53  --clausify_out                          false
% 7.67/1.53  --sig_cnt_out                           false
% 7.67/1.53  --trig_cnt_out                          false
% 7.67/1.53  --trig_cnt_out_tolerance                1.
% 7.67/1.53  --trig_cnt_out_sk_spl                   false
% 7.67/1.53  --abstr_cl_out                          false
% 7.67/1.53  
% 7.67/1.53  ------ Global Options
% 7.67/1.53  
% 7.67/1.53  --schedule                              none
% 7.67/1.53  --add_important_lit                     false
% 7.67/1.53  --prop_solver_per_cl                    1000
% 7.67/1.53  --min_unsat_core                        false
% 7.67/1.53  --soft_assumptions                      false
% 7.67/1.53  --soft_lemma_size                       3
% 7.67/1.53  --prop_impl_unit_size                   0
% 7.67/1.53  --prop_impl_unit                        []
% 7.67/1.53  --share_sel_clauses                     true
% 7.67/1.53  --reset_solvers                         false
% 7.67/1.53  --bc_imp_inh                            [conj_cone]
% 7.67/1.53  --conj_cone_tolerance                   3.
% 7.67/1.53  --extra_neg_conj                        none
% 7.67/1.53  --large_theory_mode                     true
% 7.67/1.53  --prolific_symb_bound                   200
% 7.67/1.53  --lt_threshold                          2000
% 7.67/1.53  --clause_weak_htbl                      true
% 7.67/1.53  --gc_record_bc_elim                     false
% 7.67/1.53  
% 7.67/1.53  ------ Preprocessing Options
% 7.67/1.53  
% 7.67/1.53  --preprocessing_flag                    true
% 7.67/1.53  --time_out_prep_mult                    0.1
% 7.67/1.53  --splitting_mode                        input
% 7.67/1.53  --splitting_grd                         true
% 7.67/1.53  --splitting_cvd                         false
% 7.67/1.53  --splitting_cvd_svl                     false
% 7.67/1.53  --splitting_nvd                         32
% 7.67/1.53  --sub_typing                            true
% 7.67/1.53  --prep_gs_sim                           false
% 7.67/1.53  --prep_unflatten                        true
% 7.67/1.53  --prep_res_sim                          true
% 7.67/1.53  --prep_upred                            true
% 7.67/1.53  --prep_sem_filter                       exhaustive
% 7.67/1.53  --prep_sem_filter_out                   false
% 7.67/1.53  --pred_elim                             false
% 7.67/1.53  --res_sim_input                         true
% 7.67/1.53  --eq_ax_congr_red                       true
% 7.67/1.53  --pure_diseq_elim                       true
% 7.67/1.53  --brand_transform                       false
% 7.67/1.53  --non_eq_to_eq                          false
% 7.67/1.53  --prep_def_merge                        true
% 7.67/1.53  --prep_def_merge_prop_impl              false
% 7.67/1.53  --prep_def_merge_mbd                    true
% 7.67/1.53  --prep_def_merge_tr_red                 false
% 7.67/1.53  --prep_def_merge_tr_cl                  false
% 7.67/1.53  --smt_preprocessing                     true
% 7.67/1.53  --smt_ac_axioms                         fast
% 7.67/1.53  --preprocessed_out                      false
% 7.67/1.53  --preprocessed_stats                    false
% 7.67/1.53  
% 7.67/1.53  ------ Abstraction refinement Options
% 7.67/1.53  
% 7.67/1.53  --abstr_ref                             []
% 7.67/1.53  --abstr_ref_prep                        false
% 7.67/1.53  --abstr_ref_until_sat                   false
% 7.67/1.53  --abstr_ref_sig_restrict                funpre
% 7.67/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.53  --abstr_ref_under                       []
% 7.67/1.53  
% 7.67/1.53  ------ SAT Options
% 7.67/1.53  
% 7.67/1.53  --sat_mode                              false
% 7.67/1.53  --sat_fm_restart_options                ""
% 7.67/1.53  --sat_gr_def                            false
% 7.67/1.53  --sat_epr_types                         true
% 7.67/1.53  --sat_non_cyclic_types                  false
% 7.67/1.53  --sat_finite_models                     false
% 7.67/1.53  --sat_fm_lemmas                         false
% 7.67/1.53  --sat_fm_prep                           false
% 7.67/1.53  --sat_fm_uc_incr                        true
% 7.67/1.53  --sat_out_model                         small
% 7.67/1.53  --sat_out_clauses                       false
% 7.67/1.53  
% 7.67/1.53  ------ QBF Options
% 7.67/1.53  
% 7.67/1.53  --qbf_mode                              false
% 7.67/1.53  --qbf_elim_univ                         false
% 7.67/1.53  --qbf_dom_inst                          none
% 7.67/1.53  --qbf_dom_pre_inst                      false
% 7.67/1.53  --qbf_sk_in                             false
% 7.67/1.53  --qbf_pred_elim                         true
% 7.67/1.53  --qbf_split                             512
% 7.67/1.53  
% 7.67/1.53  ------ BMC1 Options
% 7.67/1.53  
% 7.67/1.53  --bmc1_incremental                      false
% 7.67/1.53  --bmc1_axioms                           reachable_all
% 7.67/1.53  --bmc1_min_bound                        0
% 7.67/1.53  --bmc1_max_bound                        -1
% 7.67/1.53  --bmc1_max_bound_default                -1
% 7.67/1.53  --bmc1_symbol_reachability              true
% 7.67/1.53  --bmc1_property_lemmas                  false
% 7.67/1.53  --bmc1_k_induction                      false
% 7.67/1.53  --bmc1_non_equiv_states                 false
% 7.67/1.53  --bmc1_deadlock                         false
% 7.67/1.53  --bmc1_ucm                              false
% 7.67/1.53  --bmc1_add_unsat_core                   none
% 7.67/1.53  --bmc1_unsat_core_children              false
% 7.67/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.53  --bmc1_out_stat                         full
% 7.67/1.53  --bmc1_ground_init                      false
% 7.67/1.53  --bmc1_pre_inst_next_state              false
% 7.67/1.53  --bmc1_pre_inst_state                   false
% 7.67/1.53  --bmc1_pre_inst_reach_state             false
% 7.67/1.53  --bmc1_out_unsat_core                   false
% 7.67/1.53  --bmc1_aig_witness_out                  false
% 7.67/1.53  --bmc1_verbose                          false
% 7.67/1.53  --bmc1_dump_clauses_tptp                false
% 7.67/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.53  --bmc1_dump_file                        -
% 7.67/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.53  --bmc1_ucm_extend_mode                  1
% 7.67/1.53  --bmc1_ucm_init_mode                    2
% 7.67/1.53  --bmc1_ucm_cone_mode                    none
% 7.67/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.53  --bmc1_ucm_relax_model                  4
% 7.67/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.53  --bmc1_ucm_layered_model                none
% 7.67/1.53  --bmc1_ucm_max_lemma_size               10
% 7.67/1.53  
% 7.67/1.53  ------ AIG Options
% 7.67/1.53  
% 7.67/1.53  --aig_mode                              false
% 7.67/1.53  
% 7.67/1.53  ------ Instantiation Options
% 7.67/1.53  
% 7.67/1.53  --instantiation_flag                    true
% 7.67/1.53  --inst_sos_flag                         false
% 7.67/1.53  --inst_sos_phase                        true
% 7.67/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.53  --inst_lit_sel_side                     num_symb
% 7.67/1.53  --inst_solver_per_active                1400
% 7.67/1.53  --inst_solver_calls_frac                1.
% 7.67/1.53  --inst_passive_queue_type               priority_queues
% 7.67/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.53  --inst_passive_queues_freq              [25;2]
% 7.67/1.53  --inst_dismatching                      true
% 7.67/1.53  --inst_eager_unprocessed_to_passive     true
% 7.67/1.53  --inst_prop_sim_given                   true
% 7.67/1.53  --inst_prop_sim_new                     false
% 7.67/1.53  --inst_subs_new                         false
% 7.67/1.53  --inst_eq_res_simp                      false
% 7.67/1.53  --inst_subs_given                       false
% 7.67/1.53  --inst_orphan_elimination               true
% 7.67/1.53  --inst_learning_loop_flag               true
% 7.67/1.53  --inst_learning_start                   3000
% 7.67/1.53  --inst_learning_factor                  2
% 7.67/1.53  --inst_start_prop_sim_after_learn       3
% 7.67/1.53  --inst_sel_renew                        solver
% 7.67/1.53  --inst_lit_activity_flag                true
% 7.67/1.53  --inst_restr_to_given                   false
% 7.67/1.53  --inst_activity_threshold               500
% 7.67/1.53  --inst_out_proof                        true
% 7.67/1.53  
% 7.67/1.53  ------ Resolution Options
% 7.67/1.53  
% 7.67/1.53  --resolution_flag                       true
% 7.67/1.53  --res_lit_sel                           adaptive
% 7.67/1.53  --res_lit_sel_side                      none
% 7.67/1.53  --res_ordering                          kbo
% 7.67/1.53  --res_to_prop_solver                    active
% 7.67/1.53  --res_prop_simpl_new                    false
% 7.67/1.53  --res_prop_simpl_given                  true
% 7.67/1.53  --res_passive_queue_type                priority_queues
% 7.67/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.53  --res_passive_queues_freq               [15;5]
% 7.67/1.53  --res_forward_subs                      full
% 7.67/1.53  --res_backward_subs                     full
% 7.67/1.53  --res_forward_subs_resolution           true
% 7.67/1.53  --res_backward_subs_resolution          true
% 7.67/1.53  --res_orphan_elimination                true
% 7.67/1.53  --res_time_limit                        2.
% 7.67/1.53  --res_out_proof                         true
% 7.67/1.53  
% 7.67/1.53  ------ Superposition Options
% 7.67/1.53  
% 7.67/1.53  --superposition_flag                    true
% 7.67/1.53  --sup_passive_queue_type                priority_queues
% 7.67/1.53  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.53  --sup_passive_queues_freq               [1;4]
% 7.67/1.53  --demod_completeness_check              fast
% 7.67/1.53  --demod_use_ground                      true
% 7.67/1.53  --sup_to_prop_solver                    passive
% 7.67/1.53  --sup_prop_simpl_new                    true
% 7.67/1.53  --sup_prop_simpl_given                  true
% 7.67/1.53  --sup_fun_splitting                     false
% 7.67/1.53  --sup_smt_interval                      50000
% 7.67/1.53  
% 7.67/1.53  ------ Superposition Simplification Setup
% 7.67/1.53  
% 7.67/1.53  --sup_indices_passive                   []
% 7.67/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.53  --sup_full_bw                           [BwDemod]
% 7.67/1.53  --sup_immed_triv                        [TrivRules]
% 7.67/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.53  --sup_immed_bw_main                     []
% 7.67/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.67/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.67/1.53  
% 7.67/1.53  ------ Combination Options
% 7.67/1.53  
% 7.67/1.53  --comb_res_mult                         3
% 7.67/1.53  --comb_sup_mult                         2
% 7.67/1.53  --comb_inst_mult                        10
% 7.67/1.53  
% 7.67/1.53  ------ Debug Options
% 7.67/1.53  
% 7.67/1.53  --dbg_backtrace                         false
% 7.67/1.53  --dbg_dump_prop_clauses                 false
% 7.67/1.53  --dbg_dump_prop_clauses_file            -
% 7.67/1.53  --dbg_out_stat                          false
% 7.67/1.53  
% 7.67/1.53  
% 7.67/1.53  
% 7.67/1.53  
% 7.67/1.53  ------ Proving...
% 7.67/1.53  
% 7.67/1.53  
% 7.67/1.53  % SZS status Theorem for theBenchmark.p
% 7.67/1.53  
% 7.67/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 7.67/1.53  
% 7.67/1.53  fof(f8,conjecture,(
% 7.67/1.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 7.67/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.53  
% 7.67/1.53  fof(f9,negated_conjecture,(
% 7.67/1.53    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 7.67/1.53    inference(negated_conjecture,[],[f8])).
% 7.67/1.53  
% 7.67/1.53  fof(f17,plain,(
% 7.67/1.53    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 7.67/1.53    inference(ennf_transformation,[],[f9])).
% 7.67/1.53  
% 7.67/1.53  fof(f18,plain,(
% 7.67/1.53    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.67/1.53    inference(flattening,[],[f17])).
% 7.67/1.53  
% 7.67/1.53  fof(f28,plain,(
% 7.67/1.53    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK4,sK2) != k1_funct_1(k7_relat_1(sK4,sK3),sK2) & r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3))) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 7.67/1.53    introduced(choice_axiom,[])).
% 7.67/1.53  
% 7.67/1.53  fof(f29,plain,(
% 7.67/1.53    k1_funct_1(sK4,sK2) != k1_funct_1(k7_relat_1(sK4,sK3),sK2) & r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3))) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 7.67/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f28])).
% 7.67/1.53  
% 7.67/1.53  fof(f49,plain,(
% 7.67/1.53    v1_funct_1(sK4)),
% 7.67/1.53    inference(cnf_transformation,[],[f29])).
% 7.67/1.53  
% 7.67/1.53  fof(f50,plain,(
% 7.67/1.53    r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3)))),
% 7.67/1.53    inference(cnf_transformation,[],[f29])).
% 7.67/1.53  
% 7.67/1.53  fof(f3,axiom,(
% 7.67/1.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 7.67/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.53  
% 7.67/1.53  fof(f11,plain,(
% 7.67/1.53    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 7.67/1.53    inference(ennf_transformation,[],[f3])).
% 7.67/1.53  
% 7.67/1.53  fof(f24,plain,(
% 7.67/1.53    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 7.67/1.53    inference(nnf_transformation,[],[f11])).
% 7.67/1.53  
% 7.67/1.53  fof(f25,plain,(
% 7.67/1.53    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 7.67/1.53    inference(flattening,[],[f24])).
% 7.67/1.53  
% 7.67/1.53  fof(f38,plain,(
% 7.67/1.53    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 7.67/1.53    inference(cnf_transformation,[],[f25])).
% 7.67/1.53  
% 7.67/1.53  fof(f48,plain,(
% 7.67/1.53    v1_relat_1(sK4)),
% 7.67/1.53    inference(cnf_transformation,[],[f29])).
% 7.67/1.53  
% 7.67/1.53  fof(f2,axiom,(
% 7.67/1.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.67/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.53  
% 7.67/1.53  fof(f36,plain,(
% 7.67/1.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.67/1.53    inference(cnf_transformation,[],[f2])).
% 7.67/1.53  
% 7.67/1.53  fof(f6,axiom,(
% 7.67/1.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 7.67/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.53  
% 7.67/1.53  fof(f13,plain,(
% 7.67/1.53    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.67/1.53    inference(ennf_transformation,[],[f6])).
% 7.67/1.53  
% 7.67/1.53  fof(f14,plain,(
% 7.67/1.53    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.67/1.53    inference(flattening,[],[f13])).
% 7.67/1.53  
% 7.67/1.53  fof(f44,plain,(
% 7.67/1.53    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.67/1.53    inference(cnf_transformation,[],[f14])).
% 7.67/1.53  
% 7.67/1.53  fof(f5,axiom,(
% 7.67/1.53    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.67/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.53  
% 7.67/1.53  fof(f42,plain,(
% 7.67/1.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.67/1.53    inference(cnf_transformation,[],[f5])).
% 7.67/1.53  
% 7.67/1.53  fof(f43,plain,(
% 7.67/1.53    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 7.67/1.53    inference(cnf_transformation,[],[f5])).
% 7.67/1.53  
% 7.67/1.53  fof(f7,axiom,(
% 7.67/1.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 7.67/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.53  
% 7.67/1.53  fof(f15,plain,(
% 7.67/1.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.67/1.53    inference(ennf_transformation,[],[f7])).
% 7.67/1.53  
% 7.67/1.53  fof(f16,plain,(
% 7.67/1.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.67/1.53    inference(flattening,[],[f15])).
% 7.67/1.53  
% 7.67/1.53  fof(f26,plain,(
% 7.67/1.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.67/1.53    inference(nnf_transformation,[],[f16])).
% 7.67/1.53  
% 7.67/1.53  fof(f27,plain,(
% 7.67/1.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.67/1.53    inference(flattening,[],[f26])).
% 7.67/1.53  
% 7.67/1.53  fof(f47,plain,(
% 7.67/1.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.67/1.53    inference(cnf_transformation,[],[f27])).
% 7.67/1.53  
% 7.67/1.53  fof(f56,plain,(
% 7.67/1.53    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.67/1.53    inference(equality_resolution,[],[f47])).
% 7.67/1.53  
% 7.67/1.53  fof(f1,axiom,(
% 7.67/1.53    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 7.67/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.53  
% 7.67/1.53  fof(f10,plain,(
% 7.67/1.53    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 7.67/1.53    inference(ennf_transformation,[],[f1])).
% 7.67/1.53  
% 7.67/1.53  fof(f19,plain,(
% 7.67/1.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : (((X2 != X3 | ~r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 7.67/1.53    inference(nnf_transformation,[],[f10])).
% 7.67/1.53  
% 7.67/1.53  fof(f20,plain,(
% 7.67/1.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 7.67/1.53    inference(flattening,[],[f19])).
% 7.67/1.53  
% 7.67/1.53  fof(f21,plain,(
% 7.67/1.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 7.67/1.53    inference(rectify,[],[f20])).
% 7.67/1.53  
% 7.67/1.53  fof(f22,plain,(
% 7.67/1.53    ! [X1,X0] : (? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1))) => ((sK0(X0,X1) != sK1(X0,X1) | ~r2_hidden(sK0(X0,X1),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & ((sK0(X0,X1) = sK1(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1))))),
% 7.67/1.53    introduced(choice_axiom,[])).
% 7.67/1.53  
% 7.67/1.53  fof(f23,plain,(
% 7.67/1.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ((sK0(X0,X1) != sK1(X0,X1) | ~r2_hidden(sK0(X0,X1),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & ((sK0(X0,X1) = sK1(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 7.67/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 7.67/1.53  
% 7.67/1.53  fof(f31,plain,(
% 7.67/1.53    ( ! [X4,X0,X5,X1] : (X4 = X5 | ~r2_hidden(k4_tarski(X4,X5),X1) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 7.67/1.53    inference(cnf_transformation,[],[f23])).
% 7.67/1.53  
% 7.67/1.53  fof(f54,plain,(
% 7.67/1.53    ( ! [X4,X0,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 7.67/1.53    inference(equality_resolution,[],[f31])).
% 7.67/1.53  
% 7.67/1.53  fof(f4,axiom,(
% 7.67/1.53    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 7.67/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.53  
% 7.67/1.53  fof(f12,plain,(
% 7.67/1.53    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 7.67/1.53    inference(ennf_transformation,[],[f4])).
% 7.67/1.53  
% 7.67/1.53  fof(f41,plain,(
% 7.67/1.53    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 7.67/1.53    inference(cnf_transformation,[],[f12])).
% 7.67/1.53  
% 7.67/1.53  fof(f51,plain,(
% 7.67/1.53    k1_funct_1(sK4,sK2) != k1_funct_1(k7_relat_1(sK4,sK3),sK2)),
% 7.67/1.53    inference(cnf_transformation,[],[f29])).
% 7.67/1.53  
% 7.67/1.53  cnf(c_20,negated_conjecture,
% 7.67/1.53      ( v1_funct_1(sK4) ),
% 7.67/1.53      inference(cnf_transformation,[],[f49]) ).
% 7.67/1.53  
% 7.67/1.53  cnf(c_492,plain,
% 7.67/1.53      ( v1_funct_1(sK4) = iProver_top ),
% 7.67/1.53      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.67/1.53  
% 7.67/1.53  cnf(c_19,negated_conjecture,
% 7.67/1.53      ( r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3))) ),
% 7.67/1.53      inference(cnf_transformation,[],[f50]) ).
% 7.67/1.53  
% 7.67/1.53  cnf(c_493,plain,
% 7.67/1.53      ( r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3))) = iProver_top ),
% 7.67/1.53      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.67/1.53  
% 7.67/1.53  cnf(c_10,plain,
% 7.67/1.53      ( r2_hidden(X0,X1)
% 7.67/1.53      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 7.67/1.53      | ~ v1_relat_1(X2) ),
% 7.67/1.53      inference(cnf_transformation,[],[f38]) ).
% 7.67/1.53  
% 7.67/1.53  cnf(c_501,plain,
% 7.67/1.53      ( r2_hidden(X0,X1) = iProver_top
% 7.67/1.53      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
% 7.67/1.53      | v1_relat_1(X2) != iProver_top ),
% 7.67/1.53      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.67/1.53  
% 7.67/1.53  cnf(c_1051,plain,
% 7.67/1.53      ( r2_hidden(sK2,sK3) = iProver_top
% 7.67/1.53      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.53      inference(superposition,[status(thm)],[c_493,c_501]) ).
% 7.67/1.53  
% 7.67/1.53  cnf(c_21,negated_conjecture,
% 7.67/1.53      ( v1_relat_1(sK4) ),
% 7.67/1.53      inference(cnf_transformation,[],[f48]) ).
% 7.67/1.53  
% 7.67/1.53  cnf(c_22,plain,
% 7.67/1.53      ( v1_relat_1(sK4) = iProver_top ),
% 7.67/1.53      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.67/1.53  
% 7.67/1.53  cnf(c_24,plain,
% 7.67/1.53      ( r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3))) = iProver_top ),
% 7.67/1.53      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.67/1.53  
% 7.67/1.53  cnf(c_712,plain,
% 7.67/1.53      ( ~ r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3)))
% 7.67/1.53      | r2_hidden(sK2,sK3)
% 7.67/1.53      | ~ v1_relat_1(sK4) ),
% 7.67/1.53      inference(instantiation,[status(thm)],[c_10]) ).
% 7.67/1.53  
% 7.67/1.53  cnf(c_713,plain,
% 7.67/1.53      ( r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3))) != iProver_top
% 7.67/1.53      | r2_hidden(sK2,sK3) = iProver_top
% 7.67/1.53      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.53      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 7.67/1.53  
% 7.67/1.53  cnf(c_2755,plain,
% 7.67/1.53      ( r2_hidden(sK2,sK3) = iProver_top ),
% 7.67/1.53      inference(global_propositional_subsumption,
% 7.67/1.53                [status(thm)],
% 7.67/1.53                [c_1051,c_22,c_24,c_713]) ).
% 7.67/1.53  
% 7.67/1.53  cnf(c_7,plain,
% 7.67/1.53      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.67/1.53      inference(cnf_transformation,[],[f36]) ).
% 7.67/1.53  
% 7.67/1.53  cnf(c_14,plain,
% 7.67/1.53      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.67/1.53      | ~ v1_funct_1(X2)
% 7.67/1.53      | ~ v1_funct_1(X1)
% 7.67/1.53      | ~ v1_relat_1(X1)
% 7.67/1.53      | ~ v1_relat_1(X2)
% 7.67/1.53      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 7.67/1.53      inference(cnf_transformation,[],[f44]) ).
% 7.67/1.53  
% 7.67/1.53  cnf(c_497,plain,
% 7.67/1.53      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 7.67/1.53      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 7.67/1.53      | v1_funct_1(X0) != iProver_top
% 7.67/1.53      | v1_funct_1(X1) != iProver_top
% 7.67/1.54      | v1_relat_1(X0) != iProver_top
% 7.67/1.54      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.54      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1509,plain,
% 7.67/1.54      ( k1_funct_1(X0,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X0),X2)
% 7.67/1.54      | r2_hidden(X2,X1) != iProver_top
% 7.67/1.54      | v1_funct_1(X0) != iProver_top
% 7.67/1.54      | v1_funct_1(k6_relat_1(X1)) != iProver_top
% 7.67/1.54      | v1_relat_1(X0) != iProver_top
% 7.67/1.54      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_7,c_497]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_13,plain,
% 7.67/1.54      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.67/1.54      inference(cnf_transformation,[],[f42]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_498,plain,
% 7.67/1.54      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.67/1.54      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_12,plain,
% 7.67/1.54      ( v1_funct_1(k6_relat_1(X0)) ),
% 7.67/1.54      inference(cnf_transformation,[],[f43]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_499,plain,
% 7.67/1.54      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 7.67/1.54      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1986,plain,
% 7.67/1.54      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,k1_funct_1(k6_relat_1(X0),X2))
% 7.67/1.54      | r2_hidden(X2,X0) != iProver_top
% 7.67/1.54      | v1_funct_1(X1) != iProver_top
% 7.67/1.54      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.54      inference(forward_subsumption_resolution,
% 7.67/1.54                [status(thm)],
% 7.67/1.54                [c_1509,c_498,c_499]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2760,plain,
% 7.67/1.54      ( k1_funct_1(X0,k1_funct_1(k6_relat_1(sK3),sK2)) = k1_funct_1(k5_relat_1(k6_relat_1(sK3),X0),sK2)
% 7.67/1.54      | v1_funct_1(X0) != iProver_top
% 7.67/1.54      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_2755,c_1986]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_15,plain,
% 7.67/1.54      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.67/1.54      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 7.67/1.54      | ~ v1_funct_1(X1)
% 7.67/1.54      | ~ v1_relat_1(X1) ),
% 7.67/1.54      inference(cnf_transformation,[],[f56]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_496,plain,
% 7.67/1.54      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.67/1.54      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
% 7.67/1.54      | v1_funct_1(X1) != iProver_top
% 7.67/1.54      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.54      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_4,plain,
% 7.67/1.54      ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
% 7.67/1.54      | ~ v1_relat_1(k6_relat_1(X2))
% 7.67/1.54      | X0 = X1 ),
% 7.67/1.54      inference(cnf_transformation,[],[f54]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_505,plain,
% 7.67/1.54      ( X0 = X1
% 7.67/1.54      | r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2)) != iProver_top
% 7.67/1.54      | v1_relat_1(k6_relat_1(X2)) != iProver_top ),
% 7.67/1.54      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_533,plain,
% 7.67/1.54      ( X0 = X1
% 7.67/1.54      | r2_hidden(k4_tarski(X1,X0),k6_relat_1(X2)) != iProver_top ),
% 7.67/1.54      inference(forward_subsumption_resolution,
% 7.67/1.54                [status(thm)],
% 7.67/1.54                [c_505,c_498]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2140,plain,
% 7.67/1.54      ( k1_funct_1(k6_relat_1(X0),X1) = X1
% 7.67/1.54      | r2_hidden(X1,k1_relat_1(k6_relat_1(X0))) != iProver_top
% 7.67/1.54      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 7.67/1.54      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_496,c_533]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2145,plain,
% 7.67/1.54      ( k1_funct_1(k6_relat_1(X0),X1) = X1
% 7.67/1.54      | r2_hidden(X1,X0) != iProver_top
% 7.67/1.54      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 7.67/1.54      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.67/1.54      inference(light_normalisation,[status(thm)],[c_2140,c_7]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_37,plain,
% 7.67/1.54      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.67/1.54      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_40,plain,
% 7.67/1.54      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 7.67/1.54      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2171,plain,
% 7.67/1.54      ( k1_funct_1(k6_relat_1(X0),X1) = X1
% 7.67/1.54      | r2_hidden(X1,X0) != iProver_top ),
% 7.67/1.54      inference(global_propositional_subsumption,
% 7.67/1.54                [status(thm)],
% 7.67/1.54                [c_2145,c_37,c_40]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2761,plain,
% 7.67/1.54      ( k1_funct_1(k6_relat_1(sK3),sK2) = sK2 ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_2755,c_2171]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2764,plain,
% 7.67/1.54      ( k1_funct_1(k5_relat_1(k6_relat_1(sK3),X0),sK2) = k1_funct_1(X0,sK2)
% 7.67/1.54      | v1_funct_1(X0) != iProver_top
% 7.67/1.54      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.54      inference(light_normalisation,[status(thm)],[c_2760,c_2761]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_29899,plain,
% 7.67/1.54      ( k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) = k1_funct_1(sK4,sK2)
% 7.67/1.54      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_492,c_2764]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_491,plain,
% 7.67/1.54      ( v1_relat_1(sK4) = iProver_top ),
% 7.67/1.54      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_11,plain,
% 7.67/1.54      ( ~ v1_relat_1(X0)
% 7.67/1.54      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 7.67/1.54      inference(cnf_transformation,[],[f41]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_500,plain,
% 7.67/1.54      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 7.67/1.54      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.54      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1040,plain,
% 7.67/1.54      ( k5_relat_1(k6_relat_1(X0),sK4) = k7_relat_1(sK4,X0) ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_491,c_500]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_29902,plain,
% 7.67/1.54      ( k1_funct_1(k7_relat_1(sK4,sK3),sK2) = k1_funct_1(sK4,sK2)
% 7.67/1.54      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.54      inference(demodulation,[status(thm)],[c_29899,c_1040]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_184,plain,( X0 = X0 ),theory(equality) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_848,plain,
% 7.67/1.54      ( k1_funct_1(sK4,sK2) = k1_funct_1(sK4,sK2) ),
% 7.67/1.54      inference(instantiation,[status(thm)],[c_184]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_185,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_715,plain,
% 7.67/1.54      ( k1_funct_1(k7_relat_1(sK4,sK3),sK2) != X0
% 7.67/1.54      | k1_funct_1(sK4,sK2) != X0
% 7.67/1.54      | k1_funct_1(sK4,sK2) = k1_funct_1(k7_relat_1(sK4,sK3),sK2) ),
% 7.67/1.54      inference(instantiation,[status(thm)],[c_185]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_847,plain,
% 7.67/1.54      ( k1_funct_1(k7_relat_1(sK4,sK3),sK2) != k1_funct_1(sK4,sK2)
% 7.67/1.54      | k1_funct_1(sK4,sK2) = k1_funct_1(k7_relat_1(sK4,sK3),sK2)
% 7.67/1.54      | k1_funct_1(sK4,sK2) != k1_funct_1(sK4,sK2) ),
% 7.67/1.54      inference(instantiation,[status(thm)],[c_715]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_18,negated_conjecture,
% 7.67/1.54      ( k1_funct_1(sK4,sK2) != k1_funct_1(k7_relat_1(sK4,sK3),sK2) ),
% 7.67/1.54      inference(cnf_transformation,[],[f51]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(contradiction,plain,
% 7.67/1.54      ( $false ),
% 7.67/1.54      inference(minisat,[status(thm)],[c_29902,c_848,c_847,c_18,c_22]) ).
% 7.67/1.54  
% 7.67/1.54  
% 7.67/1.54  % SZS output end CNFRefutation for theBenchmark.p
% 7.67/1.54  
% 7.67/1.54  ------                               Statistics
% 7.67/1.54  
% 7.67/1.54  ------ Selected
% 7.67/1.54  
% 7.67/1.54  total_time:                             0.778
% 7.67/1.54  
%------------------------------------------------------------------------------
