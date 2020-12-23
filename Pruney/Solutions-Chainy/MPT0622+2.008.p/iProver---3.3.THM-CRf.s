%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:29 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 610 expanded)
%              Number of clauses        :   49 ( 121 expanded)
%              Number of leaves         :   13 ( 171 expanded)
%              Depth                    :   14
%              Number of atoms          :  398 (3615 expanded)
%              Number of equality atoms :  246 (2080 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k1_tarski(X0) = k2_relat_1(X2)
              & k1_tarski(X0) = k2_relat_1(X1)
              & k1_relat_1(X1) = k1_relat_1(X2) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k1_tarski(X0) = k2_relat_1(X2)
                & k1_tarski(X0) = k2_relat_1(X1)
                & k1_relat_1(X1) = k1_relat_1(X2) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( sK4 != X1
        & k1_tarski(X0) = k2_relat_1(sK4)
        & k1_tarski(X0) = k2_relat_1(X1)
        & k1_relat_1(sK4) = k1_relat_1(X1)
        & v1_funct_1(sK4)
        & v1_relat_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k1_tarski(X0) = k2_relat_1(X2)
            & k1_tarski(X0) = k2_relat_1(X1)
            & k1_relat_1(X1) = k1_relat_1(X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( sK3 != X2
          & k1_tarski(sK2) = k2_relat_1(X2)
          & k1_tarski(sK2) = k2_relat_1(sK3)
          & k1_relat_1(sK3) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( sK3 != sK4
    & k1_tarski(sK2) = k2_relat_1(sK4)
    & k1_tarski(sK2) = k2_relat_1(sK3)
    & k1_relat_1(sK3) = k1_relat_1(sK4)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f24,f23])).

fof(f43,plain,(
    k1_relat_1(sK3) = k1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
            & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f47])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f26,f48])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f28,f48])).

fof(f58,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k3_enumset1(X0,X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f53])).

fof(f59,plain,(
    ! [X4,X0] : r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f58])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    k1_tarski(sK2) = k2_relat_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f48])).

fof(f57,plain,(
    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k2_relat_1(sK3) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f45,plain,(
    k1_tarski(sK2) = k2_relat_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k2_relat_1(sK4) ),
    inference(definition_unfolding,[],[f45,f49])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_12,negated_conjecture,
    ( k1_relat_1(sK3) = k1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_389,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_866,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK3)
    | sK4 = X0
    | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_389])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1109,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != k1_relat_1(sK3)
    | sK4 = X0
    | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_866,c_19,c_20])).

cnf(c_1110,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK3)
    | sK4 = X0
    | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1109])).

cnf(c_1121,plain,
    ( sK4 = sK3
    | r2_hidden(sK1(sK3,sK4),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1110])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_552,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,X0))
    | sK3 = X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_709,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK3))
    | sK3 = sK4
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_552])).

cnf(c_3,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_710,plain,
    ( r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_649,plain,
    ( r2_hidden(sK1(sK3,X0),k1_relat_1(sK3))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | X0 = sK3
    | k1_relat_1(sK3) != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_841,plain,
    ( r2_hidden(sK1(sK3,sK4),k1_relat_1(sK3))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3 ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_842,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3
    | r2_hidden(sK1(sK3,sK4),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_841])).

cnf(c_147,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_532,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_1014,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_532])).

cnf(c_1203,plain,
    ( r2_hidden(sK1(sK3,sK4),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1121,c_17,c_18,c_19,c_20,c_12,c_9,c_709,c_710,c_842,c_1014])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_391,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11,negated_conjecture,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k2_relat_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_392,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1042,plain,
    ( sK2 = X0
    | r2_hidden(X0,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_392])).

cnf(c_1353,plain,
    ( k1_funct_1(sK3,X0) = sK2
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_391,c_1042])).

cnf(c_1589,plain,
    ( k1_funct_1(sK3,X0) = sK2
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1353,c_17,c_18])).

cnf(c_1598,plain,
    ( k1_funct_1(sK3,sK1(sK3,sK4)) = sK2 ),
    inference(superposition,[status(thm)],[c_1203,c_1589])).

cnf(c_10,negated_conjecture,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k2_relat_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_412,plain,
    ( k2_relat_1(sK3) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_10,c_11])).

cnf(c_1352,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_412,c_391])).

cnf(c_1366,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1352,c_12])).

cnf(c_1428,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1366,c_19,c_20])).

cnf(c_1436,plain,
    ( k1_funct_1(sK4,X0) = sK2
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1428,c_1042])).

cnf(c_1573,plain,
    ( k1_funct_1(sK4,sK1(sK3,sK4)) = sK2 ),
    inference(superposition,[status(thm)],[c_1203,c_1436])).

cnf(c_1100,plain,
    ( k1_funct_1(sK4,sK1(sK3,sK4)) != X0
    | k1_funct_1(sK4,sK1(sK3,sK4)) = k1_funct_1(sK3,sK1(sK3,sK4))
    | k1_funct_1(sK3,sK1(sK3,sK4)) != X0 ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_1101,plain,
    ( k1_funct_1(sK4,sK1(sK3,sK4)) = k1_funct_1(sK3,sK1(sK3,sK4))
    | k1_funct_1(sK4,sK1(sK3,sK4)) != sK2
    | k1_funct_1(sK3,sK1(sK3,sK4)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1100])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_641,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | X0 = sK3
    | k1_funct_1(X0,sK1(sK3,X0)) != k1_funct_1(sK3,sK1(sK3,X0))
    | k1_relat_1(sK3) != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_851,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_funct_1(sK4,sK1(sK3,sK4)) != k1_funct_1(sK3,sK1(sK3,sK4))
    | k1_relat_1(sK3) != k1_relat_1(sK4)
    | sK4 = sK3 ),
    inference(instantiation,[status(thm)],[c_641])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1598,c_1573,c_1101,c_1014,c_851,c_710,c_709,c_9,c_12,c_13,c_14,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n008.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 15:20:15 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.79/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/0.98  
% 1.79/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.79/0.98  
% 1.79/0.98  ------  iProver source info
% 1.79/0.98  
% 1.79/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.79/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.79/0.98  git: non_committed_changes: false
% 1.79/0.98  git: last_make_outside_of_git: false
% 1.79/0.98  
% 1.79/0.98  ------ 
% 1.79/0.98  
% 1.79/0.98  ------ Input Options
% 1.79/0.98  
% 1.79/0.98  --out_options                           all
% 1.79/0.98  --tptp_safe_out                         true
% 1.79/0.98  --problem_path                          ""
% 1.79/0.98  --include_path                          ""
% 1.79/0.98  --clausifier                            res/vclausify_rel
% 1.79/0.98  --clausifier_options                    --mode clausify
% 1.79/0.98  --stdin                                 false
% 1.79/0.98  --stats_out                             all
% 1.79/0.98  
% 1.79/0.98  ------ General Options
% 1.79/0.98  
% 1.79/0.98  --fof                                   false
% 1.79/0.98  --time_out_real                         305.
% 1.79/0.98  --time_out_virtual                      -1.
% 1.79/0.98  --symbol_type_check                     false
% 1.79/0.98  --clausify_out                          false
% 1.79/0.98  --sig_cnt_out                           false
% 1.79/0.98  --trig_cnt_out                          false
% 1.79/0.98  --trig_cnt_out_tolerance                1.
% 1.79/0.98  --trig_cnt_out_sk_spl                   false
% 1.79/0.98  --abstr_cl_out                          false
% 1.79/0.98  
% 1.79/0.98  ------ Global Options
% 1.79/0.98  
% 1.79/0.98  --schedule                              default
% 1.79/0.98  --add_important_lit                     false
% 1.79/0.98  --prop_solver_per_cl                    1000
% 1.79/0.98  --min_unsat_core                        false
% 1.79/0.98  --soft_assumptions                      false
% 1.79/0.98  --soft_lemma_size                       3
% 1.79/0.98  --prop_impl_unit_size                   0
% 1.79/0.98  --prop_impl_unit                        []
% 1.79/0.98  --share_sel_clauses                     true
% 1.79/0.98  --reset_solvers                         false
% 1.79/0.98  --bc_imp_inh                            [conj_cone]
% 1.79/0.98  --conj_cone_tolerance                   3.
% 1.79/0.98  --extra_neg_conj                        none
% 1.79/0.98  --large_theory_mode                     true
% 1.79/0.98  --prolific_symb_bound                   200
% 1.79/0.98  --lt_threshold                          2000
% 1.79/0.98  --clause_weak_htbl                      true
% 1.79/0.98  --gc_record_bc_elim                     false
% 1.79/0.98  
% 1.79/0.98  ------ Preprocessing Options
% 1.79/0.98  
% 1.79/0.98  --preprocessing_flag                    true
% 1.79/0.98  --time_out_prep_mult                    0.1
% 1.79/0.98  --splitting_mode                        input
% 1.79/0.98  --splitting_grd                         true
% 1.79/0.98  --splitting_cvd                         false
% 1.79/0.98  --splitting_cvd_svl                     false
% 1.79/0.98  --splitting_nvd                         32
% 1.79/0.98  --sub_typing                            true
% 1.79/0.98  --prep_gs_sim                           true
% 1.79/0.98  --prep_unflatten                        true
% 1.79/0.98  --prep_res_sim                          true
% 1.79/0.98  --prep_upred                            true
% 1.79/0.98  --prep_sem_filter                       exhaustive
% 1.79/0.98  --prep_sem_filter_out                   false
% 1.79/0.98  --pred_elim                             true
% 1.79/0.98  --res_sim_input                         true
% 1.79/0.98  --eq_ax_congr_red                       true
% 1.79/0.98  --pure_diseq_elim                       true
% 1.79/0.98  --brand_transform                       false
% 1.79/0.98  --non_eq_to_eq                          false
% 1.79/0.98  --prep_def_merge                        true
% 1.79/0.98  --prep_def_merge_prop_impl              false
% 1.79/0.98  --prep_def_merge_mbd                    true
% 1.79/0.98  --prep_def_merge_tr_red                 false
% 1.79/0.98  --prep_def_merge_tr_cl                  false
% 1.79/0.98  --smt_preprocessing                     true
% 1.79/0.98  --smt_ac_axioms                         fast
% 1.79/0.98  --preprocessed_out                      false
% 1.79/0.98  --preprocessed_stats                    false
% 1.79/0.98  
% 1.79/0.98  ------ Abstraction refinement Options
% 1.79/0.98  
% 1.79/0.98  --abstr_ref                             []
% 1.79/0.98  --abstr_ref_prep                        false
% 1.79/0.98  --abstr_ref_until_sat                   false
% 1.79/0.98  --abstr_ref_sig_restrict                funpre
% 1.79/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.79/0.98  --abstr_ref_under                       []
% 1.79/0.98  
% 1.79/0.98  ------ SAT Options
% 1.79/0.98  
% 1.79/0.98  --sat_mode                              false
% 1.79/0.98  --sat_fm_restart_options                ""
% 1.79/0.98  --sat_gr_def                            false
% 1.79/0.98  --sat_epr_types                         true
% 1.79/0.98  --sat_non_cyclic_types                  false
% 1.79/0.98  --sat_finite_models                     false
% 1.79/0.98  --sat_fm_lemmas                         false
% 1.79/0.98  --sat_fm_prep                           false
% 1.79/0.98  --sat_fm_uc_incr                        true
% 1.79/0.98  --sat_out_model                         small
% 1.79/0.98  --sat_out_clauses                       false
% 1.79/0.98  
% 1.79/0.98  ------ QBF Options
% 1.79/0.98  
% 1.79/0.98  --qbf_mode                              false
% 1.79/0.98  --qbf_elim_univ                         false
% 1.79/0.98  --qbf_dom_inst                          none
% 1.79/0.98  --qbf_dom_pre_inst                      false
% 1.79/0.98  --qbf_sk_in                             false
% 1.79/0.98  --qbf_pred_elim                         true
% 1.79/0.98  --qbf_split                             512
% 1.79/0.98  
% 1.79/0.98  ------ BMC1 Options
% 1.79/0.98  
% 1.79/0.98  --bmc1_incremental                      false
% 1.79/0.98  --bmc1_axioms                           reachable_all
% 1.79/0.98  --bmc1_min_bound                        0
% 1.79/0.98  --bmc1_max_bound                        -1
% 1.79/0.98  --bmc1_max_bound_default                -1
% 1.79/0.98  --bmc1_symbol_reachability              true
% 1.79/0.98  --bmc1_property_lemmas                  false
% 1.79/0.98  --bmc1_k_induction                      false
% 1.79/0.98  --bmc1_non_equiv_states                 false
% 1.79/0.98  --bmc1_deadlock                         false
% 1.79/0.98  --bmc1_ucm                              false
% 1.79/0.98  --bmc1_add_unsat_core                   none
% 1.79/0.98  --bmc1_unsat_core_children              false
% 1.79/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.79/0.98  --bmc1_out_stat                         full
% 1.79/0.98  --bmc1_ground_init                      false
% 1.79/0.98  --bmc1_pre_inst_next_state              false
% 1.79/0.98  --bmc1_pre_inst_state                   false
% 1.79/0.98  --bmc1_pre_inst_reach_state             false
% 1.79/0.98  --bmc1_out_unsat_core                   false
% 1.79/0.98  --bmc1_aig_witness_out                  false
% 1.79/0.98  --bmc1_verbose                          false
% 1.79/0.98  --bmc1_dump_clauses_tptp                false
% 1.79/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.79/0.98  --bmc1_dump_file                        -
% 1.79/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.79/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.79/0.98  --bmc1_ucm_extend_mode                  1
% 1.79/0.98  --bmc1_ucm_init_mode                    2
% 1.79/0.98  --bmc1_ucm_cone_mode                    none
% 1.79/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.79/0.98  --bmc1_ucm_relax_model                  4
% 1.79/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.79/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.79/0.98  --bmc1_ucm_layered_model                none
% 1.79/0.98  --bmc1_ucm_max_lemma_size               10
% 1.79/0.98  
% 1.79/0.98  ------ AIG Options
% 1.79/0.98  
% 1.79/0.98  --aig_mode                              false
% 1.79/0.98  
% 1.79/0.98  ------ Instantiation Options
% 1.79/0.98  
% 1.79/0.98  --instantiation_flag                    true
% 1.79/0.98  --inst_sos_flag                         false
% 1.79/0.98  --inst_sos_phase                        true
% 1.79/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.79/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.79/0.98  --inst_lit_sel_side                     num_symb
% 1.79/0.98  --inst_solver_per_active                1400
% 1.79/0.98  --inst_solver_calls_frac                1.
% 1.79/0.98  --inst_passive_queue_type               priority_queues
% 1.79/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.79/0.98  --inst_passive_queues_freq              [25;2]
% 1.79/0.98  --inst_dismatching                      true
% 1.79/0.98  --inst_eager_unprocessed_to_passive     true
% 1.79/0.98  --inst_prop_sim_given                   true
% 1.79/0.98  --inst_prop_sim_new                     false
% 1.79/0.98  --inst_subs_new                         false
% 1.79/0.98  --inst_eq_res_simp                      false
% 1.79/0.98  --inst_subs_given                       false
% 1.79/0.98  --inst_orphan_elimination               true
% 1.79/0.98  --inst_learning_loop_flag               true
% 1.79/0.98  --inst_learning_start                   3000
% 1.79/0.98  --inst_learning_factor                  2
% 1.79/0.98  --inst_start_prop_sim_after_learn       3
% 1.79/0.98  --inst_sel_renew                        solver
% 1.79/0.98  --inst_lit_activity_flag                true
% 1.79/0.98  --inst_restr_to_given                   false
% 1.79/0.98  --inst_activity_threshold               500
% 1.79/0.98  --inst_out_proof                        true
% 1.79/0.98  
% 1.79/0.98  ------ Resolution Options
% 1.79/0.98  
% 1.79/0.98  --resolution_flag                       true
% 1.79/0.98  --res_lit_sel                           adaptive
% 1.79/0.98  --res_lit_sel_side                      none
% 1.79/0.98  --res_ordering                          kbo
% 1.79/0.98  --res_to_prop_solver                    active
% 1.79/0.98  --res_prop_simpl_new                    false
% 1.79/0.98  --res_prop_simpl_given                  true
% 1.79/0.98  --res_passive_queue_type                priority_queues
% 1.79/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.79/0.98  --res_passive_queues_freq               [15;5]
% 1.79/0.98  --res_forward_subs                      full
% 1.79/0.98  --res_backward_subs                     full
% 1.79/0.98  --res_forward_subs_resolution           true
% 1.79/0.98  --res_backward_subs_resolution          true
% 1.79/0.98  --res_orphan_elimination                true
% 1.79/0.98  --res_time_limit                        2.
% 1.79/0.98  --res_out_proof                         true
% 1.79/0.98  
% 1.79/0.98  ------ Superposition Options
% 1.79/0.98  
% 1.79/0.98  --superposition_flag                    true
% 1.79/0.98  --sup_passive_queue_type                priority_queues
% 1.79/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.79/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.79/0.98  --demod_completeness_check              fast
% 1.79/0.98  --demod_use_ground                      true
% 1.79/0.98  --sup_to_prop_solver                    passive
% 1.79/0.98  --sup_prop_simpl_new                    true
% 1.79/0.98  --sup_prop_simpl_given                  true
% 1.79/0.98  --sup_fun_splitting                     false
% 1.79/0.98  --sup_smt_interval                      50000
% 1.79/0.98  
% 1.79/0.98  ------ Superposition Simplification Setup
% 1.79/0.98  
% 1.79/0.98  --sup_indices_passive                   []
% 1.79/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.79/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.98  --sup_full_bw                           [BwDemod]
% 1.79/0.98  --sup_immed_triv                        [TrivRules]
% 1.79/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.79/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.98  --sup_immed_bw_main                     []
% 1.79/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.79/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/0.98  
% 1.79/0.98  ------ Combination Options
% 1.79/0.98  
% 1.79/0.98  --comb_res_mult                         3
% 1.79/0.98  --comb_sup_mult                         2
% 1.79/0.98  --comb_inst_mult                        10
% 1.79/0.98  
% 1.79/0.98  ------ Debug Options
% 1.79/0.98  
% 1.79/0.98  --dbg_backtrace                         false
% 1.79/0.98  --dbg_dump_prop_clauses                 false
% 1.79/0.98  --dbg_dump_prop_clauses_file            -
% 1.79/0.98  --dbg_out_stat                          false
% 1.79/0.98  ------ Parsing...
% 1.79/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.79/0.98  
% 1.79/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.79/0.98  
% 1.79/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.79/0.98  
% 1.79/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.79/0.98  ------ Proving...
% 1.79/0.98  ------ Problem Properties 
% 1.79/0.98  
% 1.79/0.98  
% 1.79/0.98  clauses                                 17
% 1.79/0.98  conjectures                             8
% 1.79/0.98  EPR                                     5
% 1.79/0.98  Horn                                    14
% 1.79/0.98  unary                                   10
% 1.79/0.98  binary                                  0
% 1.79/0.98  lits                                    41
% 1.79/0.98  lits eq                                 18
% 1.79/0.98  fd_pure                                 0
% 1.79/0.98  fd_pseudo                               0
% 1.79/0.98  fd_cond                                 0
% 1.79/0.98  fd_pseudo_cond                          5
% 1.79/0.98  AC symbols                              0
% 1.79/0.98  
% 1.79/0.98  ------ Schedule dynamic 5 is on 
% 1.79/0.98  
% 1.79/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.79/0.98  
% 1.79/0.98  
% 1.79/0.98  ------ 
% 1.79/0.98  Current options:
% 1.79/0.98  ------ 
% 1.79/0.98  
% 1.79/0.98  ------ Input Options
% 1.79/0.98  
% 1.79/0.98  --out_options                           all
% 1.79/0.98  --tptp_safe_out                         true
% 1.79/0.98  --problem_path                          ""
% 1.79/0.98  --include_path                          ""
% 1.79/0.98  --clausifier                            res/vclausify_rel
% 1.79/0.98  --clausifier_options                    --mode clausify
% 1.79/0.98  --stdin                                 false
% 1.79/0.98  --stats_out                             all
% 1.79/0.98  
% 1.79/0.98  ------ General Options
% 1.79/0.98  
% 1.79/0.98  --fof                                   false
% 1.79/0.98  --time_out_real                         305.
% 1.79/0.98  --time_out_virtual                      -1.
% 1.79/0.98  --symbol_type_check                     false
% 1.79/0.98  --clausify_out                          false
% 1.79/0.98  --sig_cnt_out                           false
% 1.79/0.98  --trig_cnt_out                          false
% 1.79/0.98  --trig_cnt_out_tolerance                1.
% 1.79/0.98  --trig_cnt_out_sk_spl                   false
% 1.79/0.98  --abstr_cl_out                          false
% 1.79/0.98  
% 1.79/0.98  ------ Global Options
% 1.79/0.98  
% 1.79/0.98  --schedule                              default
% 1.79/0.98  --add_important_lit                     false
% 1.79/0.98  --prop_solver_per_cl                    1000
% 1.79/0.98  --min_unsat_core                        false
% 1.79/0.98  --soft_assumptions                      false
% 1.79/0.98  --soft_lemma_size                       3
% 1.79/0.98  --prop_impl_unit_size                   0
% 1.79/0.98  --prop_impl_unit                        []
% 1.79/0.98  --share_sel_clauses                     true
% 1.79/0.98  --reset_solvers                         false
% 1.79/0.98  --bc_imp_inh                            [conj_cone]
% 1.79/0.98  --conj_cone_tolerance                   3.
% 1.79/0.98  --extra_neg_conj                        none
% 1.79/0.98  --large_theory_mode                     true
% 1.79/0.98  --prolific_symb_bound                   200
% 1.79/0.98  --lt_threshold                          2000
% 1.79/0.98  --clause_weak_htbl                      true
% 1.79/0.98  --gc_record_bc_elim                     false
% 1.79/0.98  
% 1.79/0.98  ------ Preprocessing Options
% 1.79/0.98  
% 1.79/0.98  --preprocessing_flag                    true
% 1.79/0.98  --time_out_prep_mult                    0.1
% 1.79/0.98  --splitting_mode                        input
% 1.79/0.98  --splitting_grd                         true
% 1.79/0.98  --splitting_cvd                         false
% 1.79/0.98  --splitting_cvd_svl                     false
% 1.79/0.98  --splitting_nvd                         32
% 1.79/0.98  --sub_typing                            true
% 1.79/0.98  --prep_gs_sim                           true
% 1.79/0.98  --prep_unflatten                        true
% 1.79/0.98  --prep_res_sim                          true
% 1.79/0.98  --prep_upred                            true
% 1.79/0.98  --prep_sem_filter                       exhaustive
% 1.79/0.98  --prep_sem_filter_out                   false
% 1.79/0.98  --pred_elim                             true
% 1.79/0.98  --res_sim_input                         true
% 1.79/0.98  --eq_ax_congr_red                       true
% 1.79/0.98  --pure_diseq_elim                       true
% 1.79/0.98  --brand_transform                       false
% 1.79/0.98  --non_eq_to_eq                          false
% 1.79/0.98  --prep_def_merge                        true
% 1.79/0.98  --prep_def_merge_prop_impl              false
% 1.79/0.98  --prep_def_merge_mbd                    true
% 1.79/0.98  --prep_def_merge_tr_red                 false
% 1.79/0.98  --prep_def_merge_tr_cl                  false
% 1.79/0.98  --smt_preprocessing                     true
% 1.79/0.98  --smt_ac_axioms                         fast
% 1.79/0.98  --preprocessed_out                      false
% 1.79/0.98  --preprocessed_stats                    false
% 1.79/0.98  
% 1.79/0.98  ------ Abstraction refinement Options
% 1.79/0.98  
% 1.79/0.98  --abstr_ref                             []
% 1.79/0.98  --abstr_ref_prep                        false
% 1.79/0.98  --abstr_ref_until_sat                   false
% 1.79/0.98  --abstr_ref_sig_restrict                funpre
% 1.79/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.79/0.98  --abstr_ref_under                       []
% 1.79/0.98  
% 1.79/0.98  ------ SAT Options
% 1.79/0.98  
% 1.79/0.98  --sat_mode                              false
% 1.79/0.98  --sat_fm_restart_options                ""
% 1.79/0.98  --sat_gr_def                            false
% 1.79/0.98  --sat_epr_types                         true
% 1.79/0.98  --sat_non_cyclic_types                  false
% 1.79/0.98  --sat_finite_models                     false
% 1.79/0.98  --sat_fm_lemmas                         false
% 1.79/0.98  --sat_fm_prep                           false
% 1.79/0.98  --sat_fm_uc_incr                        true
% 1.79/0.98  --sat_out_model                         small
% 1.79/0.98  --sat_out_clauses                       false
% 1.79/0.98  
% 1.79/0.98  ------ QBF Options
% 1.79/0.98  
% 1.79/0.98  --qbf_mode                              false
% 1.79/0.98  --qbf_elim_univ                         false
% 1.79/0.98  --qbf_dom_inst                          none
% 1.79/0.98  --qbf_dom_pre_inst                      false
% 1.79/0.98  --qbf_sk_in                             false
% 1.79/0.98  --qbf_pred_elim                         true
% 1.79/0.98  --qbf_split                             512
% 1.79/0.98  
% 1.79/0.98  ------ BMC1 Options
% 1.79/0.98  
% 1.79/0.98  --bmc1_incremental                      false
% 1.79/0.98  --bmc1_axioms                           reachable_all
% 1.79/0.98  --bmc1_min_bound                        0
% 1.79/0.98  --bmc1_max_bound                        -1
% 1.79/0.98  --bmc1_max_bound_default                -1
% 1.79/0.98  --bmc1_symbol_reachability              true
% 1.79/0.98  --bmc1_property_lemmas                  false
% 1.79/0.98  --bmc1_k_induction                      false
% 1.79/0.98  --bmc1_non_equiv_states                 false
% 1.79/0.98  --bmc1_deadlock                         false
% 1.79/0.98  --bmc1_ucm                              false
% 1.79/0.98  --bmc1_add_unsat_core                   none
% 1.79/0.98  --bmc1_unsat_core_children              false
% 1.79/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.79/0.98  --bmc1_out_stat                         full
% 1.79/0.98  --bmc1_ground_init                      false
% 1.79/0.98  --bmc1_pre_inst_next_state              false
% 1.79/0.98  --bmc1_pre_inst_state                   false
% 1.79/0.98  --bmc1_pre_inst_reach_state             false
% 1.79/0.98  --bmc1_out_unsat_core                   false
% 1.79/0.98  --bmc1_aig_witness_out                  false
% 1.79/0.98  --bmc1_verbose                          false
% 1.79/0.98  --bmc1_dump_clauses_tptp                false
% 1.79/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.79/0.98  --bmc1_dump_file                        -
% 1.79/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.79/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.79/0.98  --bmc1_ucm_extend_mode                  1
% 1.79/0.98  --bmc1_ucm_init_mode                    2
% 1.79/0.98  --bmc1_ucm_cone_mode                    none
% 1.79/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.79/0.98  --bmc1_ucm_relax_model                  4
% 1.79/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.79/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.79/0.98  --bmc1_ucm_layered_model                none
% 1.79/0.98  --bmc1_ucm_max_lemma_size               10
% 1.79/0.98  
% 1.79/0.98  ------ AIG Options
% 1.79/0.98  
% 1.79/0.98  --aig_mode                              false
% 1.79/0.98  
% 1.79/0.98  ------ Instantiation Options
% 1.79/0.98  
% 1.79/0.98  --instantiation_flag                    true
% 1.79/0.98  --inst_sos_flag                         false
% 1.79/0.98  --inst_sos_phase                        true
% 1.79/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.79/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.79/0.98  --inst_lit_sel_side                     none
% 1.79/0.98  --inst_solver_per_active                1400
% 1.79/0.98  --inst_solver_calls_frac                1.
% 1.79/0.98  --inst_passive_queue_type               priority_queues
% 1.79/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.79/0.98  --inst_passive_queues_freq              [25;2]
% 1.79/0.98  --inst_dismatching                      true
% 1.79/0.98  --inst_eager_unprocessed_to_passive     true
% 1.79/0.98  --inst_prop_sim_given                   true
% 1.79/0.98  --inst_prop_sim_new                     false
% 1.79/0.98  --inst_subs_new                         false
% 1.79/0.98  --inst_eq_res_simp                      false
% 1.79/0.98  --inst_subs_given                       false
% 1.79/0.98  --inst_orphan_elimination               true
% 1.79/0.98  --inst_learning_loop_flag               true
% 1.79/0.98  --inst_learning_start                   3000
% 1.79/0.98  --inst_learning_factor                  2
% 1.79/0.98  --inst_start_prop_sim_after_learn       3
% 1.79/0.98  --inst_sel_renew                        solver
% 1.79/0.98  --inst_lit_activity_flag                true
% 1.79/0.98  --inst_restr_to_given                   false
% 1.79/0.98  --inst_activity_threshold               500
% 1.79/0.98  --inst_out_proof                        true
% 1.79/0.98  
% 1.79/0.98  ------ Resolution Options
% 1.79/0.98  
% 1.79/0.98  --resolution_flag                       false
% 1.79/0.98  --res_lit_sel                           adaptive
% 1.79/0.98  --res_lit_sel_side                      none
% 1.79/0.98  --res_ordering                          kbo
% 1.79/0.98  --res_to_prop_solver                    active
% 1.79/0.98  --res_prop_simpl_new                    false
% 1.79/0.98  --res_prop_simpl_given                  true
% 1.79/0.98  --res_passive_queue_type                priority_queues
% 1.79/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.79/0.98  --res_passive_queues_freq               [15;5]
% 1.79/0.98  --res_forward_subs                      full
% 1.79/0.98  --res_backward_subs                     full
% 1.79/0.98  --res_forward_subs_resolution           true
% 1.79/0.98  --res_backward_subs_resolution          true
% 1.79/0.98  --res_orphan_elimination                true
% 1.79/0.98  --res_time_limit                        2.
% 1.79/0.98  --res_out_proof                         true
% 1.79/0.98  
% 1.79/0.98  ------ Superposition Options
% 1.79/0.98  
% 1.79/0.98  --superposition_flag                    true
% 1.79/0.98  --sup_passive_queue_type                priority_queues
% 1.79/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.79/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.79/0.98  --demod_completeness_check              fast
% 1.79/0.98  --demod_use_ground                      true
% 1.79/0.98  --sup_to_prop_solver                    passive
% 1.79/0.98  --sup_prop_simpl_new                    true
% 1.79/0.98  --sup_prop_simpl_given                  true
% 1.79/0.98  --sup_fun_splitting                     false
% 1.79/0.98  --sup_smt_interval                      50000
% 1.79/0.98  
% 1.79/0.98  ------ Superposition Simplification Setup
% 1.79/0.98  
% 1.79/0.98  --sup_indices_passive                   []
% 1.79/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.79/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.98  --sup_full_bw                           [BwDemod]
% 1.79/0.98  --sup_immed_triv                        [TrivRules]
% 1.79/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.79/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.98  --sup_immed_bw_main                     []
% 1.79/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.79/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/0.98  
% 1.79/0.98  ------ Combination Options
% 1.79/0.98  
% 1.79/0.98  --comb_res_mult                         3
% 1.79/0.98  --comb_sup_mult                         2
% 1.79/0.98  --comb_inst_mult                        10
% 1.79/0.98  
% 1.79/0.98  ------ Debug Options
% 1.79/0.98  
% 1.79/0.98  --dbg_backtrace                         false
% 1.79/0.98  --dbg_dump_prop_clauses                 false
% 1.79/0.98  --dbg_dump_prop_clauses_file            -
% 1.79/0.98  --dbg_out_stat                          false
% 1.79/0.98  
% 1.79/0.98  
% 1.79/0.98  
% 1.79/0.98  
% 1.79/0.98  ------ Proving...
% 1.79/0.98  
% 1.79/0.98  
% 1.79/0.98  % SZS status Theorem for theBenchmark.p
% 1.79/0.98  
% 1.79/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.79/0.98  
% 1.79/0.98  fof(f8,conjecture,(
% 1.79/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2)) => X1 = X2)))),
% 1.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/0.98  
% 1.79/0.98  fof(f9,negated_conjecture,(
% 1.79/0.98    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2)) => X1 = X2)))),
% 1.79/0.98    inference(negated_conjecture,[],[f8])).
% 1.79/0.98  
% 1.79/0.98  fof(f14,plain,(
% 1.79/0.98    ? [X0,X1] : (? [X2] : ((X1 != X2 & (k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.79/0.98    inference(ennf_transformation,[],[f9])).
% 1.79/0.98  
% 1.79/0.98  fof(f15,plain,(
% 1.79/0.98    ? [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.79/0.98    inference(flattening,[],[f14])).
% 1.79/0.98  
% 1.79/0.98  fof(f24,plain,(
% 1.79/0.98    ( ! [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) => (sK4 != X1 & k1_tarski(X0) = k2_relat_1(sK4) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(sK4) = k1_relat_1(X1) & v1_funct_1(sK4) & v1_relat_1(sK4))) )),
% 1.79/0.98    introduced(choice_axiom,[])).
% 1.79/0.98  
% 1.79/0.98  fof(f23,plain,(
% 1.79/0.98    ? [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (sK3 != X2 & k1_tarski(sK2) = k2_relat_1(X2) & k1_tarski(sK2) = k2_relat_1(sK3) & k1_relat_1(sK3) = k1_relat_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 1.79/0.98    introduced(choice_axiom,[])).
% 1.79/0.98  
% 1.79/0.98  fof(f25,plain,(
% 1.79/0.98    (sK3 != sK4 & k1_tarski(sK2) = k2_relat_1(sK4) & k1_tarski(sK2) = k2_relat_1(sK3) & k1_relat_1(sK3) = k1_relat_1(sK4) & v1_funct_1(sK4) & v1_relat_1(sK4)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 1.79/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f24,f23])).
% 1.79/0.98  
% 1.79/0.98  fof(f43,plain,(
% 1.79/0.98    k1_relat_1(sK3) = k1_relat_1(sK4)),
% 1.79/0.98    inference(cnf_transformation,[],[f25])).
% 1.79/0.98  
% 1.79/0.98  fof(f7,axiom,(
% 1.79/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/0.98  
% 1.79/0.98  fof(f12,plain,(
% 1.79/0.98    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.79/0.98    inference(ennf_transformation,[],[f7])).
% 1.79/0.98  
% 1.79/0.98  fof(f13,plain,(
% 1.79/0.98    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.79/0.98    inference(flattening,[],[f12])).
% 1.79/0.98  
% 1.79/0.98  fof(f21,plain,(
% 1.79/0.98    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 1.79/0.98    introduced(choice_axiom,[])).
% 1.79/0.98  
% 1.79/0.98  fof(f22,plain,(
% 1.79/0.98    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.79/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f21])).
% 1.79/0.98  
% 1.79/0.98  fof(f37,plain,(
% 1.79/0.98    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.79/0.98    inference(cnf_transformation,[],[f22])).
% 1.79/0.98  
% 1.79/0.98  fof(f41,plain,(
% 1.79/0.98    v1_relat_1(sK4)),
% 1.79/0.98    inference(cnf_transformation,[],[f25])).
% 1.79/0.98  
% 1.79/0.98  fof(f42,plain,(
% 1.79/0.98    v1_funct_1(sK4)),
% 1.79/0.98    inference(cnf_transformation,[],[f25])).
% 1.79/0.98  
% 1.79/0.98  fof(f39,plain,(
% 1.79/0.98    v1_relat_1(sK3)),
% 1.79/0.98    inference(cnf_transformation,[],[f25])).
% 1.79/0.98  
% 1.79/0.98  fof(f40,plain,(
% 1.79/0.98    v1_funct_1(sK3)),
% 1.79/0.98    inference(cnf_transformation,[],[f25])).
% 1.79/0.98  
% 1.79/0.98  fof(f46,plain,(
% 1.79/0.98    sK3 != sK4),
% 1.79/0.98    inference(cnf_transformation,[],[f25])).
% 1.79/0.98  
% 1.79/0.98  fof(f1,axiom,(
% 1.79/0.98    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/0.98  
% 1.79/0.98  fof(f16,plain,(
% 1.79/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.79/0.98    inference(nnf_transformation,[],[f1])).
% 1.79/0.98  
% 1.79/0.98  fof(f17,plain,(
% 1.79/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.79/0.98    inference(flattening,[],[f16])).
% 1.79/0.98  
% 1.79/0.98  fof(f18,plain,(
% 1.79/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.79/0.98    inference(rectify,[],[f17])).
% 1.79/0.98  
% 1.79/0.98  fof(f19,plain,(
% 1.79/0.98    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.79/0.98    introduced(choice_axiom,[])).
% 1.79/0.98  
% 1.79/0.98  fof(f20,plain,(
% 1.79/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.79/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 1.79/0.98  
% 1.79/0.98  fof(f26,plain,(
% 1.79/0.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.79/0.98    inference(cnf_transformation,[],[f20])).
% 1.79/0.98  
% 1.79/0.98  fof(f3,axiom,(
% 1.79/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/0.98  
% 1.79/0.98  fof(f33,plain,(
% 1.79/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.79/0.98    inference(cnf_transformation,[],[f3])).
% 1.79/0.98  
% 1.79/0.98  fof(f4,axiom,(
% 1.79/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/0.98  
% 1.79/0.98  fof(f34,plain,(
% 1.79/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.79/0.98    inference(cnf_transformation,[],[f4])).
% 1.79/0.98  
% 1.79/0.98  fof(f5,axiom,(
% 1.79/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/0.98  
% 1.79/0.98  fof(f35,plain,(
% 1.79/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.79/0.98    inference(cnf_transformation,[],[f5])).
% 1.79/0.98  
% 1.79/0.98  fof(f47,plain,(
% 1.79/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.79/0.98    inference(definition_unfolding,[],[f34,f35])).
% 1.79/0.98  
% 1.79/0.98  fof(f48,plain,(
% 1.79/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.79/0.98    inference(definition_unfolding,[],[f33,f47])).
% 1.79/0.98  
% 1.79/0.98  fof(f55,plain,(
% 1.79/0.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 1.79/0.98    inference(definition_unfolding,[],[f26,f48])).
% 1.79/0.98  
% 1.79/0.98  fof(f62,plain,(
% 1.79/0.98    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.79/0.98    inference(equality_resolution,[],[f55])).
% 1.79/0.98  
% 1.79/0.98  fof(f28,plain,(
% 1.79/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.79/0.98    inference(cnf_transformation,[],[f20])).
% 1.79/0.98  
% 1.79/0.98  fof(f53,plain,(
% 1.79/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 1.79/0.98    inference(definition_unfolding,[],[f28,f48])).
% 1.79/0.98  
% 1.79/0.98  fof(f58,plain,(
% 1.79/0.98    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k3_enumset1(X0,X0,X0,X0,X4) != X2) )),
% 1.79/0.99    inference(equality_resolution,[],[f53])).
% 1.79/0.99  
% 1.79/0.99  fof(f59,plain,(
% 1.79/0.99    ( ! [X4,X0] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X4))) )),
% 1.79/0.99    inference(equality_resolution,[],[f58])).
% 1.79/0.99  
% 1.79/0.99  fof(f6,axiom,(
% 1.79/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/0.99  
% 1.79/0.99  fof(f10,plain,(
% 1.79/0.99    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.79/0.99    inference(ennf_transformation,[],[f6])).
% 1.79/0.99  
% 1.79/0.99  fof(f11,plain,(
% 1.79/0.99    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.79/0.99    inference(flattening,[],[f10])).
% 1.79/0.99  
% 1.79/0.99  fof(f36,plain,(
% 1.79/0.99    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.79/0.99    inference(cnf_transformation,[],[f11])).
% 1.79/0.99  
% 1.79/0.99  fof(f44,plain,(
% 1.79/0.99    k1_tarski(sK2) = k2_relat_1(sK3)),
% 1.79/0.99    inference(cnf_transformation,[],[f25])).
% 1.79/0.99  
% 1.79/0.99  fof(f2,axiom,(
% 1.79/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/0.99  
% 1.79/0.99  fof(f32,plain,(
% 1.79/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.79/0.99    inference(cnf_transformation,[],[f2])).
% 1.79/0.99  
% 1.79/0.99  fof(f49,plain,(
% 1.79/0.99    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.79/0.99    inference(definition_unfolding,[],[f32,f48])).
% 1.79/0.99  
% 1.79/0.99  fof(f57,plain,(
% 1.79/0.99    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k2_relat_1(sK3)),
% 1.79/0.99    inference(definition_unfolding,[],[f44,f49])).
% 1.79/0.99  
% 1.79/0.99  fof(f45,plain,(
% 1.79/0.99    k1_tarski(sK2) = k2_relat_1(sK4)),
% 1.79/0.99    inference(cnf_transformation,[],[f25])).
% 1.79/0.99  
% 1.79/0.99  fof(f56,plain,(
% 1.79/0.99    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k2_relat_1(sK4)),
% 1.79/0.99    inference(definition_unfolding,[],[f45,f49])).
% 1.79/0.99  
% 1.79/0.99  fof(f38,plain,(
% 1.79/0.99    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.79/0.99    inference(cnf_transformation,[],[f22])).
% 1.79/0.99  
% 1.79/0.99  cnf(c_12,negated_conjecture,
% 1.79/0.99      ( k1_relat_1(sK3) = k1_relat_1(sK4) ),
% 1.79/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_8,plain,
% 1.79/0.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 1.79/0.99      | ~ v1_relat_1(X1)
% 1.79/0.99      | ~ v1_relat_1(X0)
% 1.79/0.99      | ~ v1_funct_1(X1)
% 1.79/0.99      | ~ v1_funct_1(X0)
% 1.79/0.99      | X1 = X0
% 1.79/0.99      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 1.79/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_389,plain,
% 1.79/0.99      ( X0 = X1
% 1.79/0.99      | k1_relat_1(X1) != k1_relat_1(X0)
% 1.79/0.99      | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
% 1.79/0.99      | v1_relat_1(X0) != iProver_top
% 1.79/0.99      | v1_relat_1(X1) != iProver_top
% 1.79/0.99      | v1_funct_1(X0) != iProver_top
% 1.79/0.99      | v1_funct_1(X1) != iProver_top ),
% 1.79/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_866,plain,
% 1.79/0.99      ( k1_relat_1(X0) != k1_relat_1(sK3)
% 1.79/0.99      | sK4 = X0
% 1.79/0.99      | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
% 1.79/0.99      | v1_relat_1(X0) != iProver_top
% 1.79/0.99      | v1_relat_1(sK4) != iProver_top
% 1.79/0.99      | v1_funct_1(X0) != iProver_top
% 1.79/0.99      | v1_funct_1(sK4) != iProver_top ),
% 1.79/0.99      inference(superposition,[status(thm)],[c_12,c_389]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_14,negated_conjecture,
% 1.79/0.99      ( v1_relat_1(sK4) ),
% 1.79/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_19,plain,
% 1.79/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 1.79/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_13,negated_conjecture,
% 1.79/0.99      ( v1_funct_1(sK4) ),
% 1.79/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_20,plain,
% 1.79/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 1.79/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_1109,plain,
% 1.79/0.99      ( v1_funct_1(X0) != iProver_top
% 1.79/0.99      | k1_relat_1(X0) != k1_relat_1(sK3)
% 1.79/0.99      | sK4 = X0
% 1.79/0.99      | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
% 1.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 1.79/0.99      inference(global_propositional_subsumption,
% 1.79/0.99                [status(thm)],
% 1.79/0.99                [c_866,c_19,c_20]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_1110,plain,
% 1.79/0.99      ( k1_relat_1(X0) != k1_relat_1(sK3)
% 1.79/0.99      | sK4 = X0
% 1.79/0.99      | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
% 1.79/0.99      | v1_relat_1(X0) != iProver_top
% 1.79/0.99      | v1_funct_1(X0) != iProver_top ),
% 1.79/0.99      inference(renaming,[status(thm)],[c_1109]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_1121,plain,
% 1.79/0.99      ( sK4 = sK3
% 1.79/0.99      | r2_hidden(sK1(sK3,sK4),k1_relat_1(sK3)) = iProver_top
% 1.79/0.99      | v1_relat_1(sK3) != iProver_top
% 1.79/0.99      | v1_funct_1(sK3) != iProver_top ),
% 1.79/0.99      inference(equality_resolution,[status(thm)],[c_1110]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_16,negated_conjecture,
% 1.79/0.99      ( v1_relat_1(sK3) ),
% 1.79/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_17,plain,
% 1.79/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 1.79/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_15,negated_conjecture,
% 1.79/0.99      ( v1_funct_1(sK3) ),
% 1.79/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_18,plain,
% 1.79/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 1.79/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_9,negated_conjecture,
% 1.79/0.99      ( sK3 != sK4 ),
% 1.79/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_5,plain,
% 1.79/0.99      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 1.79/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_552,plain,
% 1.79/0.99      ( ~ r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,X0))
% 1.79/0.99      | sK3 = X0
% 1.79/0.99      | sK3 = sK4 ),
% 1.79/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_709,plain,
% 1.79/0.99      ( ~ r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK3))
% 1.79/0.99      | sK3 = sK4
% 1.79/0.99      | sK3 = sK3 ),
% 1.79/0.99      inference(instantiation,[status(thm)],[c_552]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_3,plain,
% 1.79/0.99      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X0)) ),
% 1.79/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_710,plain,
% 1.79/0.99      ( r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK3)) ),
% 1.79/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_649,plain,
% 1.79/0.99      ( r2_hidden(sK1(sK3,X0),k1_relat_1(sK3))
% 1.79/0.99      | ~ v1_relat_1(X0)
% 1.79/0.99      | ~ v1_relat_1(sK3)
% 1.79/0.99      | ~ v1_funct_1(X0)
% 1.79/0.99      | ~ v1_funct_1(sK3)
% 1.79/0.99      | X0 = sK3
% 1.79/0.99      | k1_relat_1(sK3) != k1_relat_1(X0) ),
% 1.79/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_841,plain,
% 1.79/0.99      ( r2_hidden(sK1(sK3,sK4),k1_relat_1(sK3))
% 1.79/0.99      | ~ v1_relat_1(sK4)
% 1.79/0.99      | ~ v1_relat_1(sK3)
% 1.79/0.99      | ~ v1_funct_1(sK4)
% 1.79/0.99      | ~ v1_funct_1(sK3)
% 1.79/0.99      | k1_relat_1(sK3) != k1_relat_1(sK4)
% 1.79/0.99      | sK4 = sK3 ),
% 1.79/0.99      inference(instantiation,[status(thm)],[c_649]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_842,plain,
% 1.79/0.99      ( k1_relat_1(sK3) != k1_relat_1(sK4)
% 1.79/0.99      | sK4 = sK3
% 1.79/0.99      | r2_hidden(sK1(sK3,sK4),k1_relat_1(sK3)) = iProver_top
% 1.79/0.99      | v1_relat_1(sK4) != iProver_top
% 1.79/0.99      | v1_relat_1(sK3) != iProver_top
% 1.79/0.99      | v1_funct_1(sK4) != iProver_top
% 1.79/0.99      | v1_funct_1(sK3) != iProver_top ),
% 1.79/0.99      inference(predicate_to_equality,[status(thm)],[c_841]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_147,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_532,plain,
% 1.79/0.99      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 1.79/0.99      inference(instantiation,[status(thm)],[c_147]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_1014,plain,
% 1.79/0.99      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 1.79/0.99      inference(instantiation,[status(thm)],[c_532]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_1203,plain,
% 1.79/0.99      ( r2_hidden(sK1(sK3,sK4),k1_relat_1(sK3)) = iProver_top ),
% 1.79/0.99      inference(global_propositional_subsumption,
% 1.79/0.99                [status(thm)],
% 1.79/0.99                [c_1121,c_17,c_18,c_19,c_20,c_12,c_9,c_709,c_710,c_842,
% 1.79/0.99                 c_1014]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_6,plain,
% 1.79/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.79/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 1.79/0.99      | ~ v1_relat_1(X1)
% 1.79/0.99      | ~ v1_funct_1(X1) ),
% 1.79/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_391,plain,
% 1.79/0.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 1.79/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 1.79/0.99      | v1_relat_1(X1) != iProver_top
% 1.79/0.99      | v1_funct_1(X1) != iProver_top ),
% 1.79/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_11,negated_conjecture,
% 1.79/0.99      ( k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k2_relat_1(sK3) ),
% 1.79/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_392,plain,
% 1.79/0.99      ( X0 = X1
% 1.79/0.99      | X0 = X2
% 1.79/0.99      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2)) != iProver_top ),
% 1.79/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_1042,plain,
% 1.79/0.99      ( sK2 = X0 | r2_hidden(X0,k2_relat_1(sK3)) != iProver_top ),
% 1.79/0.99      inference(superposition,[status(thm)],[c_11,c_392]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_1353,plain,
% 1.79/0.99      ( k1_funct_1(sK3,X0) = sK2
% 1.79/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 1.79/0.99      | v1_relat_1(sK3) != iProver_top
% 1.79/0.99      | v1_funct_1(sK3) != iProver_top ),
% 1.79/0.99      inference(superposition,[status(thm)],[c_391,c_1042]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_1589,plain,
% 1.79/0.99      ( k1_funct_1(sK3,X0) = sK2
% 1.79/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 1.79/0.99      inference(global_propositional_subsumption,
% 1.79/0.99                [status(thm)],
% 1.79/0.99                [c_1353,c_17,c_18]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_1598,plain,
% 1.79/0.99      ( k1_funct_1(sK3,sK1(sK3,sK4)) = sK2 ),
% 1.79/0.99      inference(superposition,[status(thm)],[c_1203,c_1589]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_10,negated_conjecture,
% 1.79/0.99      ( k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k2_relat_1(sK4) ),
% 1.79/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_412,plain,
% 1.79/0.99      ( k2_relat_1(sK3) = k2_relat_1(sK4) ),
% 1.79/0.99      inference(light_normalisation,[status(thm)],[c_10,c_11]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_1352,plain,
% 1.79/0.99      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 1.79/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK3)) = iProver_top
% 1.79/0.99      | v1_relat_1(sK4) != iProver_top
% 1.79/0.99      | v1_funct_1(sK4) != iProver_top ),
% 1.79/0.99      inference(superposition,[status(thm)],[c_412,c_391]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_1366,plain,
% 1.79/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 1.79/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK3)) = iProver_top
% 1.79/0.99      | v1_relat_1(sK4) != iProver_top
% 1.79/0.99      | v1_funct_1(sK4) != iProver_top ),
% 1.79/0.99      inference(light_normalisation,[status(thm)],[c_1352,c_12]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_1428,plain,
% 1.79/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 1.79/0.99      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK3)) = iProver_top ),
% 1.79/0.99      inference(global_propositional_subsumption,
% 1.79/0.99                [status(thm)],
% 1.79/0.99                [c_1366,c_19,c_20]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_1436,plain,
% 1.79/0.99      ( k1_funct_1(sK4,X0) = sK2
% 1.79/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 1.79/0.99      inference(superposition,[status(thm)],[c_1428,c_1042]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_1573,plain,
% 1.79/0.99      ( k1_funct_1(sK4,sK1(sK3,sK4)) = sK2 ),
% 1.79/0.99      inference(superposition,[status(thm)],[c_1203,c_1436]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_1100,plain,
% 1.79/0.99      ( k1_funct_1(sK4,sK1(sK3,sK4)) != X0
% 1.79/0.99      | k1_funct_1(sK4,sK1(sK3,sK4)) = k1_funct_1(sK3,sK1(sK3,sK4))
% 1.79/0.99      | k1_funct_1(sK3,sK1(sK3,sK4)) != X0 ),
% 1.79/0.99      inference(instantiation,[status(thm)],[c_147]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_1101,plain,
% 1.79/0.99      ( k1_funct_1(sK4,sK1(sK3,sK4)) = k1_funct_1(sK3,sK1(sK3,sK4))
% 1.79/0.99      | k1_funct_1(sK4,sK1(sK3,sK4)) != sK2
% 1.79/0.99      | k1_funct_1(sK3,sK1(sK3,sK4)) != sK2 ),
% 1.79/0.99      inference(instantiation,[status(thm)],[c_1100]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_7,plain,
% 1.79/0.99      ( ~ v1_relat_1(X0)
% 1.79/0.99      | ~ v1_relat_1(X1)
% 1.79/0.99      | ~ v1_funct_1(X0)
% 1.79/0.99      | ~ v1_funct_1(X1)
% 1.79/0.99      | X0 = X1
% 1.79/0.99      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 1.79/0.99      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 1.79/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_641,plain,
% 1.79/0.99      ( ~ v1_relat_1(X0)
% 1.79/0.99      | ~ v1_relat_1(sK3)
% 1.79/0.99      | ~ v1_funct_1(X0)
% 1.79/0.99      | ~ v1_funct_1(sK3)
% 1.79/0.99      | X0 = sK3
% 1.79/0.99      | k1_funct_1(X0,sK1(sK3,X0)) != k1_funct_1(sK3,sK1(sK3,X0))
% 1.79/0.99      | k1_relat_1(sK3) != k1_relat_1(X0) ),
% 1.79/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(c_851,plain,
% 1.79/0.99      ( ~ v1_relat_1(sK4)
% 1.79/0.99      | ~ v1_relat_1(sK3)
% 1.79/0.99      | ~ v1_funct_1(sK4)
% 1.79/0.99      | ~ v1_funct_1(sK3)
% 1.79/0.99      | k1_funct_1(sK4,sK1(sK3,sK4)) != k1_funct_1(sK3,sK1(sK3,sK4))
% 1.79/0.99      | k1_relat_1(sK3) != k1_relat_1(sK4)
% 1.79/0.99      | sK4 = sK3 ),
% 1.79/0.99      inference(instantiation,[status(thm)],[c_641]) ).
% 1.79/0.99  
% 1.79/0.99  cnf(contradiction,plain,
% 1.79/0.99      ( $false ),
% 1.79/0.99      inference(minisat,
% 1.79/0.99                [status(thm)],
% 1.79/0.99                [c_1598,c_1573,c_1101,c_1014,c_851,c_710,c_709,c_9,c_12,
% 1.79/0.99                 c_13,c_14,c_15,c_16]) ).
% 1.79/0.99  
% 1.79/0.99  
% 1.79/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.79/0.99  
% 1.79/0.99  ------                               Statistics
% 1.79/0.99  
% 1.79/0.99  ------ General
% 1.79/0.99  
% 1.79/0.99  abstr_ref_over_cycles:                  0
% 1.79/0.99  abstr_ref_under_cycles:                 0
% 1.79/0.99  gc_basic_clause_elim:                   0
% 1.79/0.99  forced_gc_time:                         0
% 1.79/0.99  parsing_time:                           0.008
% 1.79/0.99  unif_index_cands_time:                  0.
% 1.79/0.99  unif_index_add_time:                    0.
% 1.79/0.99  orderings_time:                         0.
% 1.79/0.99  out_proof_time:                         0.011
% 1.79/0.99  total_time:                             0.083
% 1.79/0.99  num_of_symbols:                         43
% 1.79/0.99  num_of_terms:                           1747
% 1.79/0.99  
% 1.79/0.99  ------ Preprocessing
% 1.79/0.99  
% 1.79/0.99  num_of_splits:                          0
% 1.79/0.99  num_of_split_atoms:                     0
% 1.79/0.99  num_of_reused_defs:                     0
% 1.79/0.99  num_eq_ax_congr_red:                    12
% 1.79/0.99  num_of_sem_filtered_clauses:            1
% 1.79/0.99  num_of_subtypes:                        0
% 1.79/0.99  monotx_restored_types:                  0
% 1.79/0.99  sat_num_of_epr_types:                   0
% 1.79/0.99  sat_num_of_non_cyclic_types:            0
% 1.79/0.99  sat_guarded_non_collapsed_types:        0
% 1.79/0.99  num_pure_diseq_elim:                    0
% 1.79/0.99  simp_replaced_by:                       0
% 1.79/0.99  res_preprocessed:                       70
% 1.79/0.99  prep_upred:                             0
% 1.79/0.99  prep_unflattend:                        0
% 1.79/0.99  smt_new_axioms:                         0
% 1.79/0.99  pred_elim_cands:                        3
% 1.79/0.99  pred_elim:                              0
% 1.79/0.99  pred_elim_cl:                           0
% 1.79/0.99  pred_elim_cycles:                       1
% 1.79/0.99  merged_defs:                            0
% 1.79/0.99  merged_defs_ncl:                        0
% 1.79/0.99  bin_hyper_res:                          0
% 1.79/0.99  prep_cycles:                            3
% 1.79/0.99  pred_elim_time:                         0.
% 1.79/0.99  splitting_time:                         0.
% 1.79/0.99  sem_filter_time:                        0.
% 1.79/0.99  monotx_time:                            0.
% 1.79/0.99  subtype_inf_time:                       0.
% 1.79/0.99  
% 1.79/0.99  ------ Problem properties
% 1.79/0.99  
% 1.79/0.99  clauses:                                17
% 1.79/0.99  conjectures:                            8
% 1.79/0.99  epr:                                    5
% 1.79/0.99  horn:                                   14
% 1.79/0.99  ground:                                 8
% 1.79/0.99  unary:                                  10
% 1.79/0.99  binary:                                 0
% 1.79/0.99  lits:                                   41
% 1.79/0.99  lits_eq:                                18
% 1.79/0.99  fd_pure:                                0
% 1.79/0.99  fd_pseudo:                              0
% 1.79/0.99  fd_cond:                                0
% 1.79/0.99  fd_pseudo_cond:                         5
% 1.79/0.99  ac_symbols:                             0
% 1.79/0.99  
% 1.79/0.99  ------ Propositional Solver
% 1.79/0.99  
% 1.79/0.99  prop_solver_calls:                      22
% 1.79/0.99  prop_fast_solver_calls:                 444
% 1.79/0.99  smt_solver_calls:                       0
% 1.79/0.99  smt_fast_solver_calls:                  0
% 1.79/0.99  prop_num_of_clauses:                    554
% 1.79/0.99  prop_preprocess_simplified:             2150
% 1.79/0.99  prop_fo_subsumed:                       14
% 1.79/0.99  prop_solver_time:                       0.
% 1.79/0.99  smt_solver_time:                        0.
% 1.79/0.99  smt_fast_solver_time:                   0.
% 1.79/0.99  prop_fast_solver_time:                  0.
% 1.79/0.99  prop_unsat_core_time:                   0.
% 1.79/0.99  
% 1.79/0.99  ------ QBF
% 1.79/0.99  
% 1.79/0.99  qbf_q_res:                              0
% 1.79/0.99  qbf_num_tautologies:                    0
% 1.79/0.99  qbf_prep_cycles:                        0
% 1.79/0.99  
% 1.79/0.99  ------ BMC1
% 1.79/0.99  
% 1.79/0.99  bmc1_current_bound:                     -1
% 1.79/0.99  bmc1_last_solved_bound:                 -1
% 1.79/0.99  bmc1_unsat_core_size:                   -1
% 1.79/0.99  bmc1_unsat_core_parents_size:           -1
% 1.79/0.99  bmc1_merge_next_fun:                    0
% 1.79/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.79/0.99  
% 1.79/0.99  ------ Instantiation
% 1.79/0.99  
% 1.79/0.99  inst_num_of_clauses:                    170
% 1.79/0.99  inst_num_in_passive:                    10
% 1.79/0.99  inst_num_in_active:                     110
% 1.79/0.99  inst_num_in_unprocessed:                50
% 1.79/0.99  inst_num_of_loops:                      130
% 1.79/0.99  inst_num_of_learning_restarts:          0
% 1.79/0.99  inst_num_moves_active_passive:          18
% 1.79/0.99  inst_lit_activity:                      0
% 1.79/0.99  inst_lit_activity_moves:                0
% 1.79/0.99  inst_num_tautologies:                   0
% 1.79/0.99  inst_num_prop_implied:                  0
% 1.79/0.99  inst_num_existing_simplified:           0
% 1.79/0.99  inst_num_eq_res_simplified:             0
% 1.79/0.99  inst_num_child_elim:                    0
% 1.79/0.99  inst_num_of_dismatching_blockings:      38
% 1.79/0.99  inst_num_of_non_proper_insts:           189
% 1.79/0.99  inst_num_of_duplicates:                 0
% 1.79/0.99  inst_inst_num_from_inst_to_res:         0
% 1.79/0.99  inst_dismatching_checking_time:         0.
% 1.79/0.99  
% 1.79/0.99  ------ Resolution
% 1.79/0.99  
% 1.79/0.99  res_num_of_clauses:                     0
% 1.79/0.99  res_num_in_passive:                     0
% 1.79/0.99  res_num_in_active:                      0
% 1.79/0.99  res_num_of_loops:                       73
% 1.79/0.99  res_forward_subset_subsumed:            55
% 1.79/0.99  res_backward_subset_subsumed:           0
% 1.79/0.99  res_forward_subsumed:                   0
% 1.79/0.99  res_backward_subsumed:                  0
% 1.79/0.99  res_forward_subsumption_resolution:     0
% 1.79/0.99  res_backward_subsumption_resolution:    0
% 1.79/0.99  res_clause_to_clause_subsumption:       55
% 1.79/0.99  res_orphan_elimination:                 0
% 1.79/0.99  res_tautology_del:                      16
% 1.79/0.99  res_num_eq_res_simplified:              0
% 1.79/0.99  res_num_sel_changes:                    0
% 1.79/0.99  res_moves_from_active_to_pass:          0
% 1.79/0.99  
% 1.79/0.99  ------ Superposition
% 1.79/0.99  
% 1.79/0.99  sup_time_total:                         0.
% 1.79/0.99  sup_time_generating:                    0.
% 1.79/0.99  sup_time_sim_full:                      0.
% 1.79/0.99  sup_time_sim_immed:                     0.
% 1.79/0.99  
% 1.79/0.99  sup_num_of_clauses:                     35
% 1.79/0.99  sup_num_in_active:                      26
% 1.79/0.99  sup_num_in_passive:                     9
% 1.79/0.99  sup_num_of_loops:                       25
% 1.79/0.99  sup_fw_superposition:                   17
% 1.79/0.99  sup_bw_superposition:                   4
% 1.79/0.99  sup_immediate_simplified:               2
% 1.79/0.99  sup_given_eliminated:                   0
% 1.79/0.99  comparisons_done:                       0
% 1.79/0.99  comparisons_avoided:                    4
% 1.79/0.99  
% 1.79/0.99  ------ Simplifications
% 1.79/0.99  
% 1.79/0.99  
% 1.79/0.99  sim_fw_subset_subsumed:                 0
% 1.79/0.99  sim_bw_subset_subsumed:                 0
% 1.79/0.99  sim_fw_subsumed:                        0
% 1.79/0.99  sim_bw_subsumed:                        0
% 1.79/0.99  sim_fw_subsumption_res:                 0
% 1.79/0.99  sim_bw_subsumption_res:                 0
% 1.79/0.99  sim_tautology_del:                      0
% 1.79/0.99  sim_eq_tautology_del:                   5
% 1.79/0.99  sim_eq_res_simp:                        0
% 1.79/0.99  sim_fw_demodulated:                     0
% 1.79/0.99  sim_bw_demodulated:                     0
% 1.79/0.99  sim_light_normalised:                   3
% 1.79/0.99  sim_joinable_taut:                      0
% 1.79/0.99  sim_joinable_simp:                      0
% 1.79/0.99  sim_ac_normalised:                      0
% 1.79/0.99  sim_smt_subsumption:                    0
% 1.79/0.99  
%------------------------------------------------------------------------------
