%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:45 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   99 (1042 expanded)
%              Number of clauses        :   61 ( 280 expanded)
%              Number of leaves         :    8 ( 222 expanded)
%              Depth                    :   28
%              Number of atoms          :  365 (7087 expanded)
%              Number of equality atoms :  114 ( 450 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
            <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
            | ~ r2_hidden(X0,k1_relat_1(X2))
            | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) )
            | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
            | ~ r2_hidden(X0,k1_relat_1(X2))
            | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) )
            | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
            | ~ r2_hidden(X0,k1_relat_1(X2))
            | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) )
            | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ( ~ r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(X1))
          | ~ r2_hidden(X0,k1_relat_1(sK3))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,X1))) )
        & ( ( r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(X1))
            & r2_hidden(X0,k1_relat_1(sK3)) )
          | r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,X1))) )
        & v1_funct_1(sK3)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2))
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,sK1),k1_relat_1(sK2))
            | ~ r2_hidden(sK1,k1_relat_1(X2))
            | ~ r2_hidden(sK1,k1_relat_1(k5_relat_1(X2,sK2))) )
          & ( ( r2_hidden(k1_funct_1(X2,sK1),k1_relat_1(sK2))
              & r2_hidden(sK1,k1_relat_1(X2)) )
            | r2_hidden(sK1,k1_relat_1(k5_relat_1(X2,sK2))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2))
      | ~ r2_hidden(sK1,k1_relat_1(sK3))
      | ~ r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) )
    & ( ( r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2))
        & r2_hidden(sK1,k1_relat_1(sK3)) )
      | r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) )
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f28,f27])).

fof(f46,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2))
    | r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3))
    | r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2)
        & r2_hidden(sK0(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2)
            & r2_hidden(sK0(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f23,plain,(
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

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2))
    | ~ r2_hidden(sK1,k1_relat_1(sK3))
    | ~ r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2))
    | r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_668,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2)) = iProver_top
    | r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2)))
    | r2_hidden(sK1,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_667,plain,
    ( r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) = iProver_top
    | r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_666,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_665,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_670,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_994,plain,
    ( k1_relat_1(k5_relat_1(X0,sK2)) = k10_relat_1(X0,k1_relat_1(sK2))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_665,c_670])).

cnf(c_1207,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK2)) = k10_relat_1(sK3,k1_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_666,c_994])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK0(X0,X2,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_673,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK0(X0,X2,X1)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_217,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_218,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(k4_tarski(X0,X1),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_222,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
    | r2_hidden(X0,k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_218,c_15])).

cnf(c_223,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(k4_tarski(X0,X1),sK3) ),
    inference(renaming,[status(thm)],[c_222])).

cnf(c_663,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_1355,plain,
    ( r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_673,c_663])).

cnf(c_20,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1511,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1355,c_20])).

cnf(c_1512,plain,
    ( r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1511])).

cnf(c_1523,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,sK2))) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_1512])).

cnf(c_1753,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_667,c_1523])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_671,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_936,plain,
    ( k10_relat_1(sK3,k2_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_666,c_671])).

cnf(c_9,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_289,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_290,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_294,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
    | k1_funct_1(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_290,c_15])).

cnf(c_659,plain,
    ( k1_funct_1(sK3,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_1356,plain,
    ( sK0(X0,X1,sK3) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_673,c_659])).

cnf(c_2065,plain,
    ( r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top
    | sK0(X0,X1,sK3) = k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1356,c_20])).

cnf(c_2066,plain,
    ( sK0(X0,X1,sK3) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2065])).

cnf(c_2076,plain,
    ( sK0(X0,k2_relat_1(sK3),sK3) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_936,c_2066])).

cnf(c_2417,plain,
    ( sK0(sK1,k2_relat_1(sK3),sK3) = k1_funct_1(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_1753,c_2076])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_675,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
    | r2_hidden(X0,k2_relat_1(X3)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1399,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(X0,k10_relat_1(X1,X3)) = iProver_top
    | r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k2_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_673,c_675])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_43,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2850,plain,
    ( r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
    | r2_hidden(X0,k10_relat_1(X1,X3)) = iProver_top
    | r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1399,c_43])).

cnf(c_2851,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(X0,k10_relat_1(X1,X3)) = iProver_top
    | r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2850])).

cnf(c_2863,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),X0) != iProver_top
    | r2_hidden(sK1,k10_relat_1(sK3,X0)) = iProver_top
    | r2_hidden(sK1,k10_relat_1(sK3,k2_relat_1(sK3))) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2417,c_2851])).

cnf(c_2868,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),X0) != iProver_top
    | r2_hidden(sK1,k10_relat_1(sK3,X0)) = iProver_top
    | r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2863,c_936])).

cnf(c_3352,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),X0) != iProver_top
    | r2_hidden(sK1,k10_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2868,c_20,c_1753])).

cnf(c_3360,plain,
    ( r2_hidden(sK1,k10_relat_1(sK3,k1_relat_1(sK2))) = iProver_top
    | r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_668,c_3352])).

cnf(c_3366,plain,
    ( r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3360,c_1207])).

cnf(c_2077,plain,
    ( sK0(X0,k1_relat_1(sK2),sK3) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_2066])).

cnf(c_3372,plain,
    ( sK0(sK1,k1_relat_1(sK2),sK3) = k1_funct_1(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_3366,c_2077])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_674,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3691,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2)) = iProver_top
    | r2_hidden(sK1,k10_relat_1(sK3,k1_relat_1(sK2))) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3372,c_674])).

cnf(c_3695,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2)) = iProver_top
    | r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3691,c_1207])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2))
    | ~ r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2)))
    | ~ r2_hidden(sK1,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_24,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2)) != iProver_top
    | r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) != iProver_top
    | r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3695,c_3366,c_1753,c_24,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:51:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.03/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.02  
% 3.03/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.03/1.02  
% 3.03/1.02  ------  iProver source info
% 3.03/1.02  
% 3.03/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.03/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.03/1.02  git: non_committed_changes: false
% 3.03/1.02  git: last_make_outside_of_git: false
% 3.03/1.02  
% 3.03/1.02  ------ 
% 3.03/1.02  
% 3.03/1.02  ------ Input Options
% 3.03/1.02  
% 3.03/1.02  --out_options                           all
% 3.03/1.02  --tptp_safe_out                         true
% 3.03/1.02  --problem_path                          ""
% 3.03/1.02  --include_path                          ""
% 3.03/1.02  --clausifier                            res/vclausify_rel
% 3.03/1.02  --clausifier_options                    --mode clausify
% 3.03/1.02  --stdin                                 false
% 3.03/1.02  --stats_out                             all
% 3.03/1.02  
% 3.03/1.02  ------ General Options
% 3.03/1.02  
% 3.03/1.02  --fof                                   false
% 3.03/1.02  --time_out_real                         305.
% 3.03/1.02  --time_out_virtual                      -1.
% 3.03/1.02  --symbol_type_check                     false
% 3.03/1.02  --clausify_out                          false
% 3.03/1.02  --sig_cnt_out                           false
% 3.03/1.02  --trig_cnt_out                          false
% 3.03/1.02  --trig_cnt_out_tolerance                1.
% 3.03/1.02  --trig_cnt_out_sk_spl                   false
% 3.03/1.02  --abstr_cl_out                          false
% 3.03/1.02  
% 3.03/1.02  ------ Global Options
% 3.03/1.02  
% 3.03/1.02  --schedule                              default
% 3.03/1.02  --add_important_lit                     false
% 3.03/1.02  --prop_solver_per_cl                    1000
% 3.03/1.02  --min_unsat_core                        false
% 3.03/1.02  --soft_assumptions                      false
% 3.03/1.02  --soft_lemma_size                       3
% 3.03/1.02  --prop_impl_unit_size                   0
% 3.03/1.02  --prop_impl_unit                        []
% 3.03/1.02  --share_sel_clauses                     true
% 3.03/1.02  --reset_solvers                         false
% 3.03/1.02  --bc_imp_inh                            [conj_cone]
% 3.03/1.02  --conj_cone_tolerance                   3.
% 3.03/1.02  --extra_neg_conj                        none
% 3.03/1.02  --large_theory_mode                     true
% 3.03/1.02  --prolific_symb_bound                   200
% 3.03/1.02  --lt_threshold                          2000
% 3.03/1.02  --clause_weak_htbl                      true
% 3.03/1.02  --gc_record_bc_elim                     false
% 3.03/1.02  
% 3.03/1.02  ------ Preprocessing Options
% 3.03/1.02  
% 3.03/1.02  --preprocessing_flag                    true
% 3.03/1.02  --time_out_prep_mult                    0.1
% 3.03/1.02  --splitting_mode                        input
% 3.03/1.02  --splitting_grd                         true
% 3.03/1.02  --splitting_cvd                         false
% 3.03/1.02  --splitting_cvd_svl                     false
% 3.03/1.02  --splitting_nvd                         32
% 3.03/1.02  --sub_typing                            true
% 3.03/1.02  --prep_gs_sim                           true
% 3.03/1.02  --prep_unflatten                        true
% 3.03/1.02  --prep_res_sim                          true
% 3.03/1.02  --prep_upred                            true
% 3.03/1.02  --prep_sem_filter                       exhaustive
% 3.03/1.02  --prep_sem_filter_out                   false
% 3.03/1.02  --pred_elim                             true
% 3.03/1.02  --res_sim_input                         true
% 3.03/1.02  --eq_ax_congr_red                       true
% 3.03/1.02  --pure_diseq_elim                       true
% 3.03/1.02  --brand_transform                       false
% 3.03/1.02  --non_eq_to_eq                          false
% 3.03/1.02  --prep_def_merge                        true
% 3.03/1.02  --prep_def_merge_prop_impl              false
% 3.03/1.02  --prep_def_merge_mbd                    true
% 3.03/1.02  --prep_def_merge_tr_red                 false
% 3.03/1.02  --prep_def_merge_tr_cl                  false
% 3.03/1.02  --smt_preprocessing                     true
% 3.03/1.02  --smt_ac_axioms                         fast
% 3.03/1.02  --preprocessed_out                      false
% 3.03/1.02  --preprocessed_stats                    false
% 3.03/1.02  
% 3.03/1.02  ------ Abstraction refinement Options
% 3.03/1.02  
% 3.03/1.02  --abstr_ref                             []
% 3.03/1.02  --abstr_ref_prep                        false
% 3.03/1.02  --abstr_ref_until_sat                   false
% 3.03/1.02  --abstr_ref_sig_restrict                funpre
% 3.03/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/1.02  --abstr_ref_under                       []
% 3.03/1.02  
% 3.03/1.02  ------ SAT Options
% 3.03/1.02  
% 3.03/1.02  --sat_mode                              false
% 3.03/1.02  --sat_fm_restart_options                ""
% 3.03/1.02  --sat_gr_def                            false
% 3.03/1.02  --sat_epr_types                         true
% 3.03/1.02  --sat_non_cyclic_types                  false
% 3.03/1.02  --sat_finite_models                     false
% 3.03/1.02  --sat_fm_lemmas                         false
% 3.03/1.02  --sat_fm_prep                           false
% 3.03/1.02  --sat_fm_uc_incr                        true
% 3.03/1.02  --sat_out_model                         small
% 3.03/1.02  --sat_out_clauses                       false
% 3.03/1.02  
% 3.03/1.02  ------ QBF Options
% 3.03/1.02  
% 3.03/1.02  --qbf_mode                              false
% 3.03/1.02  --qbf_elim_univ                         false
% 3.03/1.02  --qbf_dom_inst                          none
% 3.03/1.02  --qbf_dom_pre_inst                      false
% 3.03/1.02  --qbf_sk_in                             false
% 3.03/1.02  --qbf_pred_elim                         true
% 3.03/1.02  --qbf_split                             512
% 3.03/1.02  
% 3.03/1.02  ------ BMC1 Options
% 3.03/1.02  
% 3.03/1.02  --bmc1_incremental                      false
% 3.03/1.02  --bmc1_axioms                           reachable_all
% 3.03/1.02  --bmc1_min_bound                        0
% 3.03/1.02  --bmc1_max_bound                        -1
% 3.03/1.02  --bmc1_max_bound_default                -1
% 3.03/1.02  --bmc1_symbol_reachability              true
% 3.03/1.02  --bmc1_property_lemmas                  false
% 3.03/1.02  --bmc1_k_induction                      false
% 3.03/1.02  --bmc1_non_equiv_states                 false
% 3.03/1.02  --bmc1_deadlock                         false
% 3.03/1.02  --bmc1_ucm                              false
% 3.03/1.02  --bmc1_add_unsat_core                   none
% 3.03/1.02  --bmc1_unsat_core_children              false
% 3.03/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/1.02  --bmc1_out_stat                         full
% 3.03/1.02  --bmc1_ground_init                      false
% 3.03/1.02  --bmc1_pre_inst_next_state              false
% 3.03/1.02  --bmc1_pre_inst_state                   false
% 3.03/1.02  --bmc1_pre_inst_reach_state             false
% 3.03/1.02  --bmc1_out_unsat_core                   false
% 3.03/1.02  --bmc1_aig_witness_out                  false
% 3.03/1.02  --bmc1_verbose                          false
% 3.03/1.02  --bmc1_dump_clauses_tptp                false
% 3.03/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.03/1.02  --bmc1_dump_file                        -
% 3.03/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.03/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.03/1.02  --bmc1_ucm_extend_mode                  1
% 3.03/1.02  --bmc1_ucm_init_mode                    2
% 3.03/1.02  --bmc1_ucm_cone_mode                    none
% 3.03/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.03/1.02  --bmc1_ucm_relax_model                  4
% 3.03/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.03/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/1.02  --bmc1_ucm_layered_model                none
% 3.03/1.02  --bmc1_ucm_max_lemma_size               10
% 3.03/1.02  
% 3.03/1.02  ------ AIG Options
% 3.03/1.02  
% 3.03/1.02  --aig_mode                              false
% 3.03/1.02  
% 3.03/1.02  ------ Instantiation Options
% 3.03/1.02  
% 3.03/1.02  --instantiation_flag                    true
% 3.03/1.02  --inst_sos_flag                         false
% 3.03/1.02  --inst_sos_phase                        true
% 3.03/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/1.02  --inst_lit_sel_side                     num_symb
% 3.03/1.02  --inst_solver_per_active                1400
% 3.03/1.02  --inst_solver_calls_frac                1.
% 3.03/1.02  --inst_passive_queue_type               priority_queues
% 3.03/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/1.02  --inst_passive_queues_freq              [25;2]
% 3.03/1.02  --inst_dismatching                      true
% 3.03/1.02  --inst_eager_unprocessed_to_passive     true
% 3.03/1.02  --inst_prop_sim_given                   true
% 3.03/1.02  --inst_prop_sim_new                     false
% 3.03/1.02  --inst_subs_new                         false
% 3.03/1.02  --inst_eq_res_simp                      false
% 3.03/1.02  --inst_subs_given                       false
% 3.03/1.02  --inst_orphan_elimination               true
% 3.03/1.02  --inst_learning_loop_flag               true
% 3.03/1.02  --inst_learning_start                   3000
% 3.03/1.02  --inst_learning_factor                  2
% 3.03/1.02  --inst_start_prop_sim_after_learn       3
% 3.03/1.02  --inst_sel_renew                        solver
% 3.03/1.02  --inst_lit_activity_flag                true
% 3.03/1.02  --inst_restr_to_given                   false
% 3.03/1.02  --inst_activity_threshold               500
% 3.03/1.02  --inst_out_proof                        true
% 3.03/1.02  
% 3.03/1.02  ------ Resolution Options
% 3.03/1.02  
% 3.03/1.02  --resolution_flag                       true
% 3.03/1.02  --res_lit_sel                           adaptive
% 3.03/1.02  --res_lit_sel_side                      none
% 3.03/1.02  --res_ordering                          kbo
% 3.03/1.02  --res_to_prop_solver                    active
% 3.03/1.02  --res_prop_simpl_new                    false
% 3.03/1.02  --res_prop_simpl_given                  true
% 3.03/1.02  --res_passive_queue_type                priority_queues
% 3.03/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/1.02  --res_passive_queues_freq               [15;5]
% 3.03/1.02  --res_forward_subs                      full
% 3.03/1.02  --res_backward_subs                     full
% 3.03/1.02  --res_forward_subs_resolution           true
% 3.03/1.02  --res_backward_subs_resolution          true
% 3.03/1.02  --res_orphan_elimination                true
% 3.03/1.02  --res_time_limit                        2.
% 3.03/1.02  --res_out_proof                         true
% 3.03/1.02  
% 3.03/1.02  ------ Superposition Options
% 3.03/1.02  
% 3.03/1.02  --superposition_flag                    true
% 3.03/1.02  --sup_passive_queue_type                priority_queues
% 3.03/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.03/1.02  --demod_completeness_check              fast
% 3.03/1.02  --demod_use_ground                      true
% 3.03/1.02  --sup_to_prop_solver                    passive
% 3.03/1.02  --sup_prop_simpl_new                    true
% 3.03/1.02  --sup_prop_simpl_given                  true
% 3.03/1.02  --sup_fun_splitting                     false
% 3.03/1.02  --sup_smt_interval                      50000
% 3.03/1.02  
% 3.03/1.02  ------ Superposition Simplification Setup
% 3.03/1.02  
% 3.03/1.02  --sup_indices_passive                   []
% 3.03/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.02  --sup_full_bw                           [BwDemod]
% 3.03/1.02  --sup_immed_triv                        [TrivRules]
% 3.03/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.02  --sup_immed_bw_main                     []
% 3.03/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.02  
% 3.03/1.02  ------ Combination Options
% 3.03/1.02  
% 3.03/1.02  --comb_res_mult                         3
% 3.03/1.02  --comb_sup_mult                         2
% 3.03/1.02  --comb_inst_mult                        10
% 3.03/1.02  
% 3.03/1.02  ------ Debug Options
% 3.03/1.02  
% 3.03/1.02  --dbg_backtrace                         false
% 3.03/1.02  --dbg_dump_prop_clauses                 false
% 3.03/1.02  --dbg_dump_prop_clauses_file            -
% 3.03/1.02  --dbg_out_stat                          false
% 3.03/1.02  ------ Parsing...
% 3.03/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.03/1.02  
% 3.03/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.03/1.02  
% 3.03/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.03/1.02  
% 3.03/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.03/1.02  ------ Proving...
% 3.03/1.02  ------ Problem Properties 
% 3.03/1.02  
% 3.03/1.02  
% 3.03/1.02  clauses                                 18
% 3.03/1.02  conjectures                             5
% 3.03/1.02  EPR                                     2
% 3.03/1.02  Horn                                    16
% 3.03/1.02  unary                                   2
% 3.03/1.02  binary                                  9
% 3.03/1.02  lits                                    43
% 3.03/1.02  lits eq                                 4
% 3.03/1.02  fd_pure                                 0
% 3.03/1.02  fd_pseudo                               0
% 3.03/1.02  fd_cond                                 0
% 3.03/1.02  fd_pseudo_cond                          2
% 3.03/1.02  AC symbols                              0
% 3.03/1.02  
% 3.03/1.02  ------ Schedule dynamic 5 is on 
% 3.03/1.02  
% 3.03/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.03/1.02  
% 3.03/1.02  
% 3.03/1.02  ------ 
% 3.03/1.02  Current options:
% 3.03/1.02  ------ 
% 3.03/1.02  
% 3.03/1.02  ------ Input Options
% 3.03/1.02  
% 3.03/1.02  --out_options                           all
% 3.03/1.02  --tptp_safe_out                         true
% 3.03/1.02  --problem_path                          ""
% 3.03/1.02  --include_path                          ""
% 3.03/1.02  --clausifier                            res/vclausify_rel
% 3.03/1.02  --clausifier_options                    --mode clausify
% 3.03/1.02  --stdin                                 false
% 3.03/1.02  --stats_out                             all
% 3.03/1.02  
% 3.03/1.02  ------ General Options
% 3.03/1.02  
% 3.03/1.02  --fof                                   false
% 3.03/1.02  --time_out_real                         305.
% 3.03/1.02  --time_out_virtual                      -1.
% 3.03/1.02  --symbol_type_check                     false
% 3.03/1.02  --clausify_out                          false
% 3.03/1.02  --sig_cnt_out                           false
% 3.03/1.02  --trig_cnt_out                          false
% 3.03/1.02  --trig_cnt_out_tolerance                1.
% 3.03/1.02  --trig_cnt_out_sk_spl                   false
% 3.03/1.02  --abstr_cl_out                          false
% 3.03/1.02  
% 3.03/1.02  ------ Global Options
% 3.03/1.02  
% 3.03/1.02  --schedule                              default
% 3.03/1.02  --add_important_lit                     false
% 3.03/1.02  --prop_solver_per_cl                    1000
% 3.03/1.02  --min_unsat_core                        false
% 3.03/1.02  --soft_assumptions                      false
% 3.03/1.02  --soft_lemma_size                       3
% 3.03/1.02  --prop_impl_unit_size                   0
% 3.03/1.02  --prop_impl_unit                        []
% 3.03/1.02  --share_sel_clauses                     true
% 3.03/1.02  --reset_solvers                         false
% 3.03/1.02  --bc_imp_inh                            [conj_cone]
% 3.03/1.02  --conj_cone_tolerance                   3.
% 3.03/1.02  --extra_neg_conj                        none
% 3.03/1.02  --large_theory_mode                     true
% 3.03/1.02  --prolific_symb_bound                   200
% 3.03/1.02  --lt_threshold                          2000
% 3.03/1.02  --clause_weak_htbl                      true
% 3.03/1.02  --gc_record_bc_elim                     false
% 3.03/1.02  
% 3.03/1.02  ------ Preprocessing Options
% 3.03/1.02  
% 3.03/1.02  --preprocessing_flag                    true
% 3.03/1.02  --time_out_prep_mult                    0.1
% 3.03/1.02  --splitting_mode                        input
% 3.03/1.02  --splitting_grd                         true
% 3.03/1.02  --splitting_cvd                         false
% 3.03/1.02  --splitting_cvd_svl                     false
% 3.03/1.02  --splitting_nvd                         32
% 3.03/1.02  --sub_typing                            true
% 3.03/1.02  --prep_gs_sim                           true
% 3.03/1.02  --prep_unflatten                        true
% 3.03/1.02  --prep_res_sim                          true
% 3.03/1.02  --prep_upred                            true
% 3.03/1.02  --prep_sem_filter                       exhaustive
% 3.03/1.02  --prep_sem_filter_out                   false
% 3.03/1.02  --pred_elim                             true
% 3.03/1.02  --res_sim_input                         true
% 3.03/1.02  --eq_ax_congr_red                       true
% 3.03/1.02  --pure_diseq_elim                       true
% 3.03/1.02  --brand_transform                       false
% 3.03/1.02  --non_eq_to_eq                          false
% 3.03/1.02  --prep_def_merge                        true
% 3.03/1.02  --prep_def_merge_prop_impl              false
% 3.03/1.02  --prep_def_merge_mbd                    true
% 3.03/1.02  --prep_def_merge_tr_red                 false
% 3.03/1.02  --prep_def_merge_tr_cl                  false
% 3.03/1.02  --smt_preprocessing                     true
% 3.03/1.02  --smt_ac_axioms                         fast
% 3.03/1.02  --preprocessed_out                      false
% 3.03/1.02  --preprocessed_stats                    false
% 3.03/1.02  
% 3.03/1.02  ------ Abstraction refinement Options
% 3.03/1.02  
% 3.03/1.02  --abstr_ref                             []
% 3.03/1.02  --abstr_ref_prep                        false
% 3.03/1.02  --abstr_ref_until_sat                   false
% 3.03/1.02  --abstr_ref_sig_restrict                funpre
% 3.03/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/1.02  --abstr_ref_under                       []
% 3.03/1.02  
% 3.03/1.02  ------ SAT Options
% 3.03/1.02  
% 3.03/1.02  --sat_mode                              false
% 3.03/1.02  --sat_fm_restart_options                ""
% 3.03/1.02  --sat_gr_def                            false
% 3.03/1.02  --sat_epr_types                         true
% 3.03/1.02  --sat_non_cyclic_types                  false
% 3.03/1.02  --sat_finite_models                     false
% 3.03/1.02  --sat_fm_lemmas                         false
% 3.03/1.02  --sat_fm_prep                           false
% 3.03/1.02  --sat_fm_uc_incr                        true
% 3.03/1.02  --sat_out_model                         small
% 3.03/1.02  --sat_out_clauses                       false
% 3.03/1.02  
% 3.03/1.02  ------ QBF Options
% 3.03/1.02  
% 3.03/1.02  --qbf_mode                              false
% 3.03/1.02  --qbf_elim_univ                         false
% 3.03/1.02  --qbf_dom_inst                          none
% 3.03/1.02  --qbf_dom_pre_inst                      false
% 3.03/1.02  --qbf_sk_in                             false
% 3.03/1.02  --qbf_pred_elim                         true
% 3.03/1.02  --qbf_split                             512
% 3.03/1.02  
% 3.03/1.02  ------ BMC1 Options
% 3.03/1.02  
% 3.03/1.02  --bmc1_incremental                      false
% 3.03/1.02  --bmc1_axioms                           reachable_all
% 3.03/1.02  --bmc1_min_bound                        0
% 3.03/1.02  --bmc1_max_bound                        -1
% 3.03/1.02  --bmc1_max_bound_default                -1
% 3.03/1.02  --bmc1_symbol_reachability              true
% 3.03/1.02  --bmc1_property_lemmas                  false
% 3.03/1.02  --bmc1_k_induction                      false
% 3.03/1.02  --bmc1_non_equiv_states                 false
% 3.03/1.02  --bmc1_deadlock                         false
% 3.03/1.02  --bmc1_ucm                              false
% 3.03/1.02  --bmc1_add_unsat_core                   none
% 3.03/1.02  --bmc1_unsat_core_children              false
% 3.03/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/1.02  --bmc1_out_stat                         full
% 3.03/1.02  --bmc1_ground_init                      false
% 3.03/1.02  --bmc1_pre_inst_next_state              false
% 3.03/1.02  --bmc1_pre_inst_state                   false
% 3.03/1.02  --bmc1_pre_inst_reach_state             false
% 3.03/1.02  --bmc1_out_unsat_core                   false
% 3.03/1.02  --bmc1_aig_witness_out                  false
% 3.03/1.02  --bmc1_verbose                          false
% 3.03/1.02  --bmc1_dump_clauses_tptp                false
% 3.03/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.03/1.02  --bmc1_dump_file                        -
% 3.03/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.03/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.03/1.02  --bmc1_ucm_extend_mode                  1
% 3.03/1.02  --bmc1_ucm_init_mode                    2
% 3.03/1.02  --bmc1_ucm_cone_mode                    none
% 3.03/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.03/1.02  --bmc1_ucm_relax_model                  4
% 3.03/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.03/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/1.02  --bmc1_ucm_layered_model                none
% 3.03/1.02  --bmc1_ucm_max_lemma_size               10
% 3.03/1.02  
% 3.03/1.02  ------ AIG Options
% 3.03/1.02  
% 3.03/1.02  --aig_mode                              false
% 3.03/1.02  
% 3.03/1.02  ------ Instantiation Options
% 3.03/1.02  
% 3.03/1.02  --instantiation_flag                    true
% 3.03/1.02  --inst_sos_flag                         false
% 3.03/1.02  --inst_sos_phase                        true
% 3.03/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/1.02  --inst_lit_sel_side                     none
% 3.03/1.02  --inst_solver_per_active                1400
% 3.03/1.02  --inst_solver_calls_frac                1.
% 3.03/1.02  --inst_passive_queue_type               priority_queues
% 3.03/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/1.02  --inst_passive_queues_freq              [25;2]
% 3.03/1.02  --inst_dismatching                      true
% 3.03/1.02  --inst_eager_unprocessed_to_passive     true
% 3.03/1.02  --inst_prop_sim_given                   true
% 3.03/1.02  --inst_prop_sim_new                     false
% 3.03/1.02  --inst_subs_new                         false
% 3.03/1.02  --inst_eq_res_simp                      false
% 3.03/1.02  --inst_subs_given                       false
% 3.03/1.02  --inst_orphan_elimination               true
% 3.03/1.02  --inst_learning_loop_flag               true
% 3.03/1.02  --inst_learning_start                   3000
% 3.03/1.02  --inst_learning_factor                  2
% 3.03/1.02  --inst_start_prop_sim_after_learn       3
% 3.03/1.02  --inst_sel_renew                        solver
% 3.03/1.02  --inst_lit_activity_flag                true
% 3.03/1.02  --inst_restr_to_given                   false
% 3.03/1.02  --inst_activity_threshold               500
% 3.03/1.02  --inst_out_proof                        true
% 3.03/1.02  
% 3.03/1.02  ------ Resolution Options
% 3.03/1.02  
% 3.03/1.02  --resolution_flag                       false
% 3.03/1.02  --res_lit_sel                           adaptive
% 3.03/1.02  --res_lit_sel_side                      none
% 3.03/1.02  --res_ordering                          kbo
% 3.03/1.02  --res_to_prop_solver                    active
% 3.03/1.02  --res_prop_simpl_new                    false
% 3.03/1.02  --res_prop_simpl_given                  true
% 3.03/1.02  --res_passive_queue_type                priority_queues
% 3.03/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/1.02  --res_passive_queues_freq               [15;5]
% 3.03/1.02  --res_forward_subs                      full
% 3.03/1.02  --res_backward_subs                     full
% 3.03/1.02  --res_forward_subs_resolution           true
% 3.03/1.02  --res_backward_subs_resolution          true
% 3.03/1.02  --res_orphan_elimination                true
% 3.03/1.02  --res_time_limit                        2.
% 3.03/1.02  --res_out_proof                         true
% 3.03/1.02  
% 3.03/1.02  ------ Superposition Options
% 3.03/1.02  
% 3.03/1.02  --superposition_flag                    true
% 3.03/1.02  --sup_passive_queue_type                priority_queues
% 3.03/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.03/1.02  --demod_completeness_check              fast
% 3.03/1.02  --demod_use_ground                      true
% 3.03/1.02  --sup_to_prop_solver                    passive
% 3.03/1.02  --sup_prop_simpl_new                    true
% 3.03/1.02  --sup_prop_simpl_given                  true
% 3.03/1.02  --sup_fun_splitting                     false
% 3.03/1.02  --sup_smt_interval                      50000
% 3.03/1.02  
% 3.03/1.02  ------ Superposition Simplification Setup
% 3.03/1.02  
% 3.03/1.02  --sup_indices_passive                   []
% 3.03/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.02  --sup_full_bw                           [BwDemod]
% 3.03/1.02  --sup_immed_triv                        [TrivRules]
% 3.03/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.02  --sup_immed_bw_main                     []
% 3.03/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/1.02  
% 3.03/1.02  ------ Combination Options
% 3.03/1.02  
% 3.03/1.02  --comb_res_mult                         3
% 3.03/1.02  --comb_sup_mult                         2
% 3.03/1.02  --comb_inst_mult                        10
% 3.03/1.02  
% 3.03/1.02  ------ Debug Options
% 3.03/1.02  
% 3.03/1.02  --dbg_backtrace                         false
% 3.03/1.02  --dbg_dump_prop_clauses                 false
% 3.03/1.02  --dbg_dump_prop_clauses_file            -
% 3.03/1.02  --dbg_out_stat                          false
% 3.03/1.02  
% 3.03/1.02  
% 3.03/1.02  
% 3.03/1.02  
% 3.03/1.02  ------ Proving...
% 3.03/1.02  
% 3.03/1.02  
% 3.03/1.02  % SZS status Theorem for theBenchmark.p
% 3.03/1.02  
% 3.03/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.03/1.02  
% 3.03/1.02  fof(f7,conjecture,(
% 3.03/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 3.03/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.02  
% 3.03/1.02  fof(f8,negated_conjecture,(
% 3.03/1.02    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 3.03/1.02    inference(negated_conjecture,[],[f7])).
% 3.03/1.02  
% 3.03/1.02  fof(f17,plain,(
% 3.03/1.02    ? [X0,X1] : (? [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <~> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.03/1.02    inference(ennf_transformation,[],[f8])).
% 3.03/1.02  
% 3.03/1.02  fof(f18,plain,(
% 3.03/1.02    ? [X0,X1] : (? [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <~> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.03/1.02    inference(flattening,[],[f17])).
% 3.03/1.02  
% 3.03/1.02  fof(f25,plain,(
% 3.03/1.02    ? [X0,X1] : (? [X2] : ((((~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.03/1.02    inference(nnf_transformation,[],[f18])).
% 3.03/1.02  
% 3.03/1.02  fof(f26,plain,(
% 3.03/1.02    ? [X0,X1] : (? [X2] : ((~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.03/1.02    inference(flattening,[],[f25])).
% 3.03/1.02  
% 3.03/1.02  fof(f28,plain,(
% 3.03/1.02    ( ! [X0,X1] : (? [X2] : ((~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & v1_funct_1(X2) & v1_relat_1(X2)) => ((~r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(sK3)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,X1)))) & ((r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(sK3))) | r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,X1)))) & v1_funct_1(sK3) & v1_relat_1(sK3))) )),
% 3.03/1.02    introduced(choice_axiom,[])).
% 3.03/1.02  
% 3.03/1.02  fof(f27,plain,(
% 3.03/1.02    ? [X0,X1] : (? [X2] : ((~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r2_hidden(k1_funct_1(X2,sK1),k1_relat_1(sK2)) | ~r2_hidden(sK1,k1_relat_1(X2)) | ~r2_hidden(sK1,k1_relat_1(k5_relat_1(X2,sK2)))) & ((r2_hidden(k1_funct_1(X2,sK1),k1_relat_1(sK2)) & r2_hidden(sK1,k1_relat_1(X2))) | r2_hidden(sK1,k1_relat_1(k5_relat_1(X2,sK2)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.03/1.02    introduced(choice_axiom,[])).
% 3.03/1.02  
% 3.03/1.02  fof(f29,plain,(
% 3.03/1.02    ((~r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2)) | ~r2_hidden(sK1,k1_relat_1(sK3)) | ~r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2)))) & ((r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2)) & r2_hidden(sK1,k1_relat_1(sK3))) | r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2)))) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.03/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f28,f27])).
% 3.03/1.02  
% 3.03/1.02  fof(f46,plain,(
% 3.03/1.02    r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2)) | r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2)))),
% 3.03/1.02    inference(cnf_transformation,[],[f29])).
% 3.03/1.02  
% 3.03/1.02  fof(f45,plain,(
% 3.03/1.02    r2_hidden(sK1,k1_relat_1(sK3)) | r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2)))),
% 3.03/1.02    inference(cnf_transformation,[],[f29])).
% 3.03/1.02  
% 3.03/1.02  fof(f43,plain,(
% 3.03/1.02    v1_relat_1(sK3)),
% 3.03/1.02    inference(cnf_transformation,[],[f29])).
% 3.03/1.02  
% 3.03/1.02  fof(f41,plain,(
% 3.03/1.02    v1_relat_1(sK2)),
% 3.03/1.02    inference(cnf_transformation,[],[f29])).
% 3.03/1.02  
% 3.03/1.02  fof(f5,axiom,(
% 3.03/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 3.03/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.02  
% 3.03/1.02  fof(f14,plain,(
% 3.03/1.02    ! [X0] : (! [X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.03/1.02    inference(ennf_transformation,[],[f5])).
% 3.03/1.02  
% 3.03/1.02  fof(f37,plain,(
% 3.03/1.02    ( ! [X0,X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.03/1.02    inference(cnf_transformation,[],[f14])).
% 3.03/1.02  
% 3.03/1.02  fof(f2,axiom,(
% 3.03/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 3.03/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.02  
% 3.03/1.02  fof(f11,plain,(
% 3.03/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.03/1.03    inference(ennf_transformation,[],[f2])).
% 3.03/1.03  
% 3.03/1.03  fof(f19,plain,(
% 3.03/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.03/1.03    inference(nnf_transformation,[],[f11])).
% 3.03/1.03  
% 3.03/1.03  fof(f20,plain,(
% 3.03/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.03/1.03    inference(rectify,[],[f19])).
% 3.03/1.03  
% 3.03/1.03  fof(f21,plain,(
% 3.03/1.03    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2) & r2_hidden(sK0(X0,X1,X2),k2_relat_1(X2))))),
% 3.03/1.03    introduced(choice_axiom,[])).
% 3.03/1.03  
% 3.03/1.03  fof(f22,plain,(
% 3.03/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2) & r2_hidden(sK0(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.03/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 3.03/1.03  
% 3.03/1.03  fof(f32,plain,(
% 3.03/1.03    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK0(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.03/1.03    inference(cnf_transformation,[],[f22])).
% 3.03/1.03  
% 3.03/1.03  fof(f6,axiom,(
% 3.03/1.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.03  
% 3.03/1.03  fof(f15,plain,(
% 3.03/1.03    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.03/1.03    inference(ennf_transformation,[],[f6])).
% 3.03/1.03  
% 3.03/1.03  fof(f16,plain,(
% 3.03/1.03    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.03/1.03    inference(flattening,[],[f15])).
% 3.03/1.03  
% 3.03/1.03  fof(f23,plain,(
% 3.03/1.03    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.03/1.03    inference(nnf_transformation,[],[f16])).
% 3.03/1.03  
% 3.03/1.03  fof(f24,plain,(
% 3.03/1.03    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.03/1.03    inference(flattening,[],[f23])).
% 3.03/1.03  
% 3.03/1.03  fof(f38,plain,(
% 3.03/1.03    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.03/1.03    inference(cnf_transformation,[],[f24])).
% 3.03/1.03  
% 3.03/1.03  fof(f44,plain,(
% 3.03/1.03    v1_funct_1(sK3)),
% 3.03/1.03    inference(cnf_transformation,[],[f29])).
% 3.03/1.03  
% 3.03/1.03  fof(f4,axiom,(
% 3.03/1.03    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 3.03/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/1.03  
% 3.03/1.03  fof(f13,plain,(
% 3.03/1.03    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 3.03/1.03    inference(ennf_transformation,[],[f4])).
% 3.03/1.03  
% 3.03/1.03  fof(f36,plain,(
% 3.03/1.03    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/1.03    inference(cnf_transformation,[],[f13])).
% 3.03/1.03  
% 3.03/1.03  fof(f39,plain,(
% 3.03/1.03    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.03/1.03    inference(cnf_transformation,[],[f24])).
% 3.03/1.03  
% 3.03/1.03  fof(f34,plain,(
% 3.03/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 3.03/1.03    inference(cnf_transformation,[],[f22])).
% 3.03/1.03  
% 3.03/1.03  fof(f31,plain,(
% 3.03/1.03    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.03/1.03    inference(cnf_transformation,[],[f22])).
% 3.03/1.03  
% 3.03/1.03  fof(f33,plain,(
% 3.03/1.03    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.03/1.03    inference(cnf_transformation,[],[f22])).
% 3.03/1.03  
% 3.03/1.03  fof(f47,plain,(
% 3.03/1.03    ~r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2)) | ~r2_hidden(sK1,k1_relat_1(sK3)) | ~r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2)))),
% 3.03/1.03    inference(cnf_transformation,[],[f29])).
% 3.03/1.03  
% 3.03/1.03  cnf(c_12,negated_conjecture,
% 3.03/1.03      ( r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2))
% 3.03/1.03      | r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) ),
% 3.03/1.03      inference(cnf_transformation,[],[f46]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_668,plain,
% 3.03/1.03      ( r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2)) = iProver_top
% 3.03/1.03      | r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) = iProver_top ),
% 3.03/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_13,negated_conjecture,
% 3.03/1.03      ( r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2)))
% 3.03/1.03      | r2_hidden(sK1,k1_relat_1(sK3)) ),
% 3.03/1.03      inference(cnf_transformation,[],[f45]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_667,plain,
% 3.03/1.03      ( r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) = iProver_top
% 3.03/1.03      | r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
% 3.03/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_15,negated_conjecture,
% 3.03/1.03      ( v1_relat_1(sK3) ),
% 3.03/1.03      inference(cnf_transformation,[],[f43]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_666,plain,
% 3.03/1.03      ( v1_relat_1(sK3) = iProver_top ),
% 3.03/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_17,negated_conjecture,
% 3.03/1.03      ( v1_relat_1(sK2) ),
% 3.03/1.03      inference(cnf_transformation,[],[f41]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_665,plain,
% 3.03/1.03      ( v1_relat_1(sK2) = iProver_top ),
% 3.03/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_7,plain,
% 3.03/1.03      ( ~ v1_relat_1(X0)
% 3.03/1.03      | ~ v1_relat_1(X1)
% 3.03/1.03      | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
% 3.03/1.03      inference(cnf_transformation,[],[f37]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_670,plain,
% 3.03/1.03      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
% 3.03/1.03      | v1_relat_1(X0) != iProver_top
% 3.03/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.03/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_994,plain,
% 3.03/1.03      ( k1_relat_1(k5_relat_1(X0,sK2)) = k10_relat_1(X0,k1_relat_1(sK2))
% 3.03/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.03/1.03      inference(superposition,[status(thm)],[c_665,c_670]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_1207,plain,
% 3.03/1.03      ( k1_relat_1(k5_relat_1(sK3,sK2)) = k10_relat_1(sK3,k1_relat_1(sK2)) ),
% 3.03/1.03      inference(superposition,[status(thm)],[c_666,c_994]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_3,plain,
% 3.03/1.03      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.03/1.03      | r2_hidden(k4_tarski(X0,sK0(X0,X2,X1)),X1)
% 3.03/1.03      | ~ v1_relat_1(X1) ),
% 3.03/1.03      inference(cnf_transformation,[],[f32]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_673,plain,
% 3.03/1.03      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.03/1.03      | r2_hidden(k4_tarski(X0,sK0(X0,X2,X1)),X1) = iProver_top
% 3.03/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.03/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_10,plain,
% 3.03/1.03      ( r2_hidden(X0,k1_relat_1(X1))
% 3.03/1.03      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.03/1.03      | ~ v1_funct_1(X1)
% 3.03/1.03      | ~ v1_relat_1(X1) ),
% 3.03/1.03      inference(cnf_transformation,[],[f38]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_14,negated_conjecture,
% 3.03/1.03      ( v1_funct_1(sK3) ),
% 3.03/1.03      inference(cnf_transformation,[],[f44]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_217,plain,
% 3.03/1.03      ( r2_hidden(X0,k1_relat_1(X1))
% 3.03/1.03      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.03/1.03      | ~ v1_relat_1(X1)
% 3.03/1.03      | sK3 != X1 ),
% 3.03/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_218,plain,
% 3.03/1.03      ( r2_hidden(X0,k1_relat_1(sK3))
% 3.03/1.03      | ~ r2_hidden(k4_tarski(X0,X1),sK3)
% 3.03/1.03      | ~ v1_relat_1(sK3) ),
% 3.03/1.03      inference(unflattening,[status(thm)],[c_217]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_222,plain,
% 3.03/1.03      ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
% 3.03/1.03      | r2_hidden(X0,k1_relat_1(sK3)) ),
% 3.03/1.03      inference(global_propositional_subsumption,
% 3.03/1.03                [status(thm)],
% 3.03/1.03                [c_218,c_15]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_223,plain,
% 3.03/1.03      ( r2_hidden(X0,k1_relat_1(sK3))
% 3.03/1.03      | ~ r2_hidden(k4_tarski(X0,X1),sK3) ),
% 3.03/1.03      inference(renaming,[status(thm)],[c_222]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_663,plain,
% 3.03/1.03      ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 3.03/1.03      | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
% 3.03/1.03      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_1355,plain,
% 3.03/1.03      ( r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top
% 3.03/1.03      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 3.03/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.03/1.03      inference(superposition,[status(thm)],[c_673,c_663]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_20,plain,
% 3.03/1.03      ( v1_relat_1(sK3) = iProver_top ),
% 3.03/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_1511,plain,
% 3.03/1.03      ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 3.03/1.03      | r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top ),
% 3.03/1.03      inference(global_propositional_subsumption,
% 3.03/1.03                [status(thm)],
% 3.03/1.03                [c_1355,c_20]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_1512,plain,
% 3.03/1.03      ( r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top
% 3.03/1.03      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
% 3.03/1.03      inference(renaming,[status(thm)],[c_1511]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_1523,plain,
% 3.03/1.03      ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,sK2))) != iProver_top
% 3.03/1.03      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
% 3.03/1.03      inference(superposition,[status(thm)],[c_1207,c_1512]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_1753,plain,
% 3.03/1.03      ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
% 3.03/1.03      inference(superposition,[status(thm)],[c_667,c_1523]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_6,plain,
% 3.03/1.03      ( ~ v1_relat_1(X0)
% 3.03/1.03      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.03/1.03      inference(cnf_transformation,[],[f36]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_671,plain,
% 3.03/1.03      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.03/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.03/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_936,plain,
% 3.03/1.03      ( k10_relat_1(sK3,k2_relat_1(sK3)) = k1_relat_1(sK3) ),
% 3.03/1.03      inference(superposition,[status(thm)],[c_666,c_671]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_9,plain,
% 3.03/1.03      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.03/1.03      | ~ v1_funct_1(X2)
% 3.03/1.03      | ~ v1_relat_1(X2)
% 3.03/1.03      | k1_funct_1(X2,X0) = X1 ),
% 3.03/1.03      inference(cnf_transformation,[],[f39]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_289,plain,
% 3.03/1.03      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.03/1.03      | ~ v1_relat_1(X2)
% 3.03/1.03      | k1_funct_1(X2,X0) = X1
% 3.03/1.03      | sK3 != X2 ),
% 3.03/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_290,plain,
% 3.03/1.03      ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
% 3.03/1.03      | ~ v1_relat_1(sK3)
% 3.03/1.03      | k1_funct_1(sK3,X0) = X1 ),
% 3.03/1.03      inference(unflattening,[status(thm)],[c_289]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_294,plain,
% 3.03/1.03      ( ~ r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1 ),
% 3.03/1.03      inference(global_propositional_subsumption,
% 3.03/1.03                [status(thm)],
% 3.03/1.03                [c_290,c_15]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_659,plain,
% 3.03/1.03      ( k1_funct_1(sK3,X0) = X1
% 3.03/1.03      | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
% 3.03/1.03      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_1356,plain,
% 3.03/1.03      ( sK0(X0,X1,sK3) = k1_funct_1(sK3,X0)
% 3.03/1.03      | r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top
% 3.03/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.03/1.03      inference(superposition,[status(thm)],[c_673,c_659]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_2065,plain,
% 3.03/1.03      ( r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top
% 3.03/1.03      | sK0(X0,X1,sK3) = k1_funct_1(sK3,X0) ),
% 3.03/1.03      inference(global_propositional_subsumption,
% 3.03/1.03                [status(thm)],
% 3.03/1.03                [c_1356,c_20]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_2066,plain,
% 3.03/1.03      ( sK0(X0,X1,sK3) = k1_funct_1(sK3,X0)
% 3.03/1.03      | r2_hidden(X0,k10_relat_1(sK3,X1)) != iProver_top ),
% 3.03/1.03      inference(renaming,[status(thm)],[c_2065]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_2076,plain,
% 3.03/1.03      ( sK0(X0,k2_relat_1(sK3),sK3) = k1_funct_1(sK3,X0)
% 3.03/1.03      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 3.03/1.03      inference(superposition,[status(thm)],[c_936,c_2066]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_2417,plain,
% 3.03/1.03      ( sK0(sK1,k2_relat_1(sK3),sK3) = k1_funct_1(sK3,sK1) ),
% 3.03/1.03      inference(superposition,[status(thm)],[c_1753,c_2076]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_1,plain,
% 3.03/1.03      ( ~ r2_hidden(X0,X1)
% 3.03/1.03      | r2_hidden(X2,k10_relat_1(X3,X1))
% 3.03/1.03      | ~ r2_hidden(X0,k2_relat_1(X3))
% 3.03/1.03      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 3.03/1.03      | ~ v1_relat_1(X3) ),
% 3.03/1.03      inference(cnf_transformation,[],[f34]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_675,plain,
% 3.03/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.03/1.03      | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
% 3.03/1.03      | r2_hidden(X0,k2_relat_1(X3)) != iProver_top
% 3.03/1.03      | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
% 3.03/1.03      | v1_relat_1(X3) != iProver_top ),
% 3.03/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_1399,plain,
% 3.03/1.03      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.03/1.03      | r2_hidden(X0,k10_relat_1(X1,X3)) = iProver_top
% 3.03/1.03      | r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
% 3.03/1.03      | r2_hidden(sK0(X0,X2,X1),k2_relat_1(X1)) != iProver_top
% 3.03/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.03/1.03      inference(superposition,[status(thm)],[c_673,c_675]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_4,plain,
% 3.03/1.03      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.03/1.03      | r2_hidden(sK0(X0,X2,X1),k2_relat_1(X1))
% 3.03/1.03      | ~ v1_relat_1(X1) ),
% 3.03/1.03      inference(cnf_transformation,[],[f31]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_43,plain,
% 3.03/1.03      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.03/1.03      | r2_hidden(sK0(X0,X2,X1),k2_relat_1(X1)) = iProver_top
% 3.03/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.03/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_2850,plain,
% 3.03/1.03      ( r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
% 3.03/1.03      | r2_hidden(X0,k10_relat_1(X1,X3)) = iProver_top
% 3.03/1.03      | r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.03/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.03/1.03      inference(global_propositional_subsumption,
% 3.03/1.03                [status(thm)],
% 3.03/1.03                [c_1399,c_43]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_2851,plain,
% 3.03/1.03      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.03/1.03      | r2_hidden(X0,k10_relat_1(X1,X3)) = iProver_top
% 3.03/1.03      | r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
% 3.03/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.03/1.03      inference(renaming,[status(thm)],[c_2850]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_2863,plain,
% 3.03/1.03      ( r2_hidden(k1_funct_1(sK3,sK1),X0) != iProver_top
% 3.03/1.03      | r2_hidden(sK1,k10_relat_1(sK3,X0)) = iProver_top
% 3.03/1.03      | r2_hidden(sK1,k10_relat_1(sK3,k2_relat_1(sK3))) != iProver_top
% 3.03/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.03/1.03      inference(superposition,[status(thm)],[c_2417,c_2851]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_2868,plain,
% 3.03/1.03      ( r2_hidden(k1_funct_1(sK3,sK1),X0) != iProver_top
% 3.03/1.03      | r2_hidden(sK1,k10_relat_1(sK3,X0)) = iProver_top
% 3.03/1.03      | r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top
% 3.03/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.03/1.03      inference(light_normalisation,[status(thm)],[c_2863,c_936]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_3352,plain,
% 3.03/1.03      ( r2_hidden(k1_funct_1(sK3,sK1),X0) != iProver_top
% 3.03/1.03      | r2_hidden(sK1,k10_relat_1(sK3,X0)) = iProver_top ),
% 3.03/1.03      inference(global_propositional_subsumption,
% 3.03/1.03                [status(thm)],
% 3.03/1.03                [c_2868,c_20,c_1753]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_3360,plain,
% 3.03/1.03      ( r2_hidden(sK1,k10_relat_1(sK3,k1_relat_1(sK2))) = iProver_top
% 3.03/1.03      | r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) = iProver_top ),
% 3.03/1.03      inference(superposition,[status(thm)],[c_668,c_3352]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_3366,plain,
% 3.03/1.03      ( r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) = iProver_top ),
% 3.03/1.03      inference(light_normalisation,[status(thm)],[c_3360,c_1207]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_2077,plain,
% 3.03/1.03      ( sK0(X0,k1_relat_1(sK2),sK3) = k1_funct_1(sK3,X0)
% 3.03/1.03      | r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,sK2))) != iProver_top ),
% 3.03/1.03      inference(superposition,[status(thm)],[c_1207,c_2066]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_3372,plain,
% 3.03/1.03      ( sK0(sK1,k1_relat_1(sK2),sK3) = k1_funct_1(sK3,sK1) ),
% 3.03/1.03      inference(superposition,[status(thm)],[c_3366,c_2077]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_2,plain,
% 3.03/1.03      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.03/1.03      | r2_hidden(sK0(X0,X2,X1),X2)
% 3.03/1.03      | ~ v1_relat_1(X1) ),
% 3.03/1.03      inference(cnf_transformation,[],[f33]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_674,plain,
% 3.03/1.03      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.03/1.03      | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
% 3.03/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.03/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_3691,plain,
% 3.03/1.03      ( r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2)) = iProver_top
% 3.03/1.03      | r2_hidden(sK1,k10_relat_1(sK3,k1_relat_1(sK2))) != iProver_top
% 3.03/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.03/1.03      inference(superposition,[status(thm)],[c_3372,c_674]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_3695,plain,
% 3.03/1.03      ( r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2)) = iProver_top
% 3.03/1.03      | r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) != iProver_top
% 3.03/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.03/1.03      inference(light_normalisation,[status(thm)],[c_3691,c_1207]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_11,negated_conjecture,
% 3.03/1.03      ( ~ r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2))
% 3.03/1.03      | ~ r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2)))
% 3.03/1.03      | ~ r2_hidden(sK1,k1_relat_1(sK3)) ),
% 3.03/1.03      inference(cnf_transformation,[],[f47]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(c_24,plain,
% 3.03/1.03      ( r2_hidden(k1_funct_1(sK3,sK1),k1_relat_1(sK2)) != iProver_top
% 3.03/1.03      | r2_hidden(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) != iProver_top
% 3.03/1.03      | r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top ),
% 3.03/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.03/1.03  
% 3.03/1.03  cnf(contradiction,plain,
% 3.03/1.03      ( $false ),
% 3.03/1.03      inference(minisat,[status(thm)],[c_3695,c_3366,c_1753,c_24,c_20]) ).
% 3.03/1.03  
% 3.03/1.03  
% 3.03/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.03/1.03  
% 3.03/1.03  ------                               Statistics
% 3.03/1.03  
% 3.03/1.03  ------ General
% 3.03/1.03  
% 3.03/1.03  abstr_ref_over_cycles:                  0
% 3.03/1.03  abstr_ref_under_cycles:                 0
% 3.03/1.03  gc_basic_clause_elim:                   0
% 3.03/1.03  forced_gc_time:                         0
% 3.03/1.03  parsing_time:                           0.008
% 3.03/1.03  unif_index_cands_time:                  0.
% 3.03/1.03  unif_index_add_time:                    0.
% 3.03/1.03  orderings_time:                         0.
% 3.03/1.03  out_proof_time:                         0.01
% 3.03/1.03  total_time:                             0.156
% 3.03/1.03  num_of_symbols:                         45
% 3.03/1.03  num_of_terms:                           3003
% 3.03/1.03  
% 3.03/1.03  ------ Preprocessing
% 3.03/1.03  
% 3.03/1.03  num_of_splits:                          0
% 3.03/1.03  num_of_split_atoms:                     0
% 3.03/1.03  num_of_reused_defs:                     0
% 3.03/1.03  num_eq_ax_congr_red:                    12
% 3.03/1.03  num_of_sem_filtered_clauses:            1
% 3.03/1.03  num_of_subtypes:                        0
% 3.03/1.03  monotx_restored_types:                  0
% 3.03/1.03  sat_num_of_epr_types:                   0
% 3.03/1.03  sat_num_of_non_cyclic_types:            0
% 3.03/1.03  sat_guarded_non_collapsed_types:        0
% 3.03/1.03  num_pure_diseq_elim:                    0
% 3.03/1.03  simp_replaced_by:                       0
% 3.03/1.03  res_preprocessed:                       73
% 3.03/1.03  prep_upred:                             0
% 3.03/1.03  prep_unflattend:                        8
% 3.03/1.03  smt_new_axioms:                         0
% 3.03/1.03  pred_elim_cands:                        4
% 3.03/1.03  pred_elim:                              2
% 3.03/1.03  pred_elim_cl:                           0
% 3.03/1.03  pred_elim_cycles:                       3
% 3.03/1.03  merged_defs:                            0
% 3.03/1.03  merged_defs_ncl:                        0
% 3.03/1.03  bin_hyper_res:                          0
% 3.03/1.03  prep_cycles:                            3
% 3.03/1.03  pred_elim_time:                         0.002
% 3.03/1.03  splitting_time:                         0.
% 3.03/1.03  sem_filter_time:                        0.
% 3.03/1.03  monotx_time:                            0.
% 3.03/1.03  subtype_inf_time:                       0.
% 3.03/1.03  
% 3.03/1.03  ------ Problem properties
% 3.03/1.03  
% 3.03/1.03  clauses:                                18
% 3.03/1.03  conjectures:                            5
% 3.03/1.03  epr:                                    2
% 3.03/1.03  horn:                                   16
% 3.03/1.03  ground:                                 5
% 3.03/1.03  unary:                                  2
% 3.03/1.03  binary:                                 9
% 3.03/1.03  lits:                                   43
% 3.03/1.03  lits_eq:                                4
% 3.03/1.03  fd_pure:                                0
% 3.03/1.03  fd_pseudo:                              0
% 3.03/1.03  fd_cond:                                0
% 3.03/1.03  fd_pseudo_cond:                         2
% 3.03/1.03  ac_symbols:                             0
% 3.03/1.03  
% 3.03/1.03  ------ Propositional Solver
% 3.03/1.03  
% 3.03/1.03  prop_solver_calls:                      28
% 3.03/1.03  prop_fast_solver_calls:                 556
% 3.03/1.03  smt_solver_calls:                       0
% 3.03/1.03  smt_fast_solver_calls:                  0
% 3.03/1.03  prop_num_of_clauses:                    1204
% 3.03/1.03  prop_preprocess_simplified:             3476
% 3.03/1.03  prop_fo_subsumed:                       19
% 3.03/1.03  prop_solver_time:                       0.
% 3.03/1.03  smt_solver_time:                        0.
% 3.03/1.03  smt_fast_solver_time:                   0.
% 3.03/1.03  prop_fast_solver_time:                  0.
% 3.03/1.03  prop_unsat_core_time:                   0.
% 3.03/1.03  
% 3.03/1.03  ------ QBF
% 3.03/1.03  
% 3.03/1.03  qbf_q_res:                              0
% 3.03/1.03  qbf_num_tautologies:                    0
% 3.03/1.03  qbf_prep_cycles:                        0
% 3.03/1.03  
% 3.03/1.03  ------ BMC1
% 3.03/1.03  
% 3.03/1.03  bmc1_current_bound:                     -1
% 3.03/1.03  bmc1_last_solved_bound:                 -1
% 3.03/1.03  bmc1_unsat_core_size:                   -1
% 3.03/1.03  bmc1_unsat_core_parents_size:           -1
% 3.03/1.03  bmc1_merge_next_fun:                    0
% 3.03/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.03/1.03  
% 3.03/1.03  ------ Instantiation
% 3.03/1.03  
% 3.03/1.03  inst_num_of_clauses:                    428
% 3.03/1.03  inst_num_in_passive:                    93
% 3.03/1.03  inst_num_in_active:                     264
% 3.03/1.03  inst_num_in_unprocessed:                71
% 3.03/1.03  inst_num_of_loops:                      290
% 3.03/1.03  inst_num_of_learning_restarts:          0
% 3.03/1.03  inst_num_moves_active_passive:          18
% 3.03/1.03  inst_lit_activity:                      0
% 3.03/1.03  inst_lit_activity_moves:                0
% 3.03/1.03  inst_num_tautologies:                   0
% 3.03/1.03  inst_num_prop_implied:                  0
% 3.03/1.03  inst_num_existing_simplified:           0
% 3.03/1.03  inst_num_eq_res_simplified:             0
% 3.03/1.03  inst_num_child_elim:                    0
% 3.03/1.03  inst_num_of_dismatching_blockings:      139
% 3.03/1.03  inst_num_of_non_proper_insts:           448
% 3.03/1.03  inst_num_of_duplicates:                 0
% 3.03/1.03  inst_inst_num_from_inst_to_res:         0
% 3.03/1.03  inst_dismatching_checking_time:         0.
% 3.03/1.03  
% 3.03/1.03  ------ Resolution
% 3.03/1.03  
% 3.03/1.03  res_num_of_clauses:                     0
% 3.03/1.03  res_num_in_passive:                     0
% 3.03/1.03  res_num_in_active:                      0
% 3.03/1.03  res_num_of_loops:                       76
% 3.03/1.03  res_forward_subset_subsumed:            86
% 3.03/1.03  res_backward_subset_subsumed:           2
% 3.03/1.03  res_forward_subsumed:                   0
% 3.03/1.03  res_backward_subsumed:                  0
% 3.03/1.03  res_forward_subsumption_resolution:     0
% 3.03/1.03  res_backward_subsumption_resolution:    0
% 3.03/1.03  res_clause_to_clause_subsumption:       185
% 3.03/1.03  res_orphan_elimination:                 0
% 3.03/1.03  res_tautology_del:                      131
% 3.03/1.03  res_num_eq_res_simplified:              0
% 3.03/1.03  res_num_sel_changes:                    0
% 3.03/1.03  res_moves_from_active_to_pass:          0
% 3.03/1.03  
% 3.03/1.03  ------ Superposition
% 3.03/1.03  
% 3.03/1.03  sup_time_total:                         0.
% 3.03/1.03  sup_time_generating:                    0.
% 3.03/1.03  sup_time_sim_full:                      0.
% 3.03/1.03  sup_time_sim_immed:                     0.
% 3.03/1.03  
% 3.03/1.03  sup_num_of_clauses:                     95
% 3.03/1.03  sup_num_in_active:                      56
% 3.03/1.03  sup_num_in_passive:                     39
% 3.03/1.03  sup_num_of_loops:                       57
% 3.03/1.03  sup_fw_superposition:                   91
% 3.03/1.03  sup_bw_superposition:                   27
% 3.03/1.03  sup_immediate_simplified:               29
% 3.03/1.03  sup_given_eliminated:                   0
% 3.03/1.03  comparisons_done:                       0
% 3.03/1.03  comparisons_avoided:                    0
% 3.03/1.03  
% 3.03/1.03  ------ Simplifications
% 3.03/1.03  
% 3.03/1.03  
% 3.03/1.03  sim_fw_subset_subsumed:                 9
% 3.03/1.03  sim_bw_subset_subsumed:                 3
% 3.03/1.03  sim_fw_subsumed:                        4
% 3.03/1.03  sim_bw_subsumed:                        0
% 3.03/1.03  sim_fw_subsumption_res:                 0
% 3.03/1.03  sim_bw_subsumption_res:                 0
% 3.03/1.03  sim_tautology_del:                      10
% 3.03/1.03  sim_eq_tautology_del:                   2
% 3.03/1.03  sim_eq_res_simp:                        0
% 3.03/1.03  sim_fw_demodulated:                     0
% 3.03/1.03  sim_bw_demodulated:                     0
% 3.03/1.03  sim_light_normalised:                   19
% 3.03/1.03  sim_joinable_taut:                      0
% 3.03/1.03  sim_joinable_simp:                      0
% 3.03/1.03  sim_ac_normalised:                      0
% 3.03/1.03  sim_smt_subsumption:                    0
% 3.03/1.03  
%------------------------------------------------------------------------------
