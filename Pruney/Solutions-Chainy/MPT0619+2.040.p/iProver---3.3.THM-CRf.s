%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:18 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 479 expanded)
%              Number of clauses        :   38 ( 109 expanded)
%              Number of leaves         :    9 ( 116 expanded)
%              Depth                    :   18
%              Number of atoms          :  317 (2146 expanded)
%              Number of equality atoms :  171 (1119 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)
      & k1_tarski(sK5) = k1_relat_1(sK6)
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)
    & k1_tarski(sK5) = k1_relat_1(sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f12,f25])).

fof(f40,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) = X0
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = X1
      | sK0(X0,X1) = X0
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f23,f22,f21])).

fof(f34,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f39,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(definition_unfolding,[],[f42,f31])).

fof(f33,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f41,plain,(
    k1_tarski(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    k2_tarski(sK5,sK5) = k1_relat_1(sK6) ),
    inference(definition_unfolding,[],[f41,f31])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f51,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) != X0
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = X1
      | sK0(X0,X1) != X0
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f35,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f53,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f49,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f45])).

fof(f50,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f49])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_353,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | sK0(X0,X1) = X0
    | k2_tarski(X0,X0) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_363,plain,
    ( sK0(X0,X1) = X0
    | k2_tarski(X0,X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_355,plain,
    ( k1_funct_1(X0,sK4(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1032,plain,
    ( k1_funct_1(X0,sK4(X0,sK0(X1,k2_relat_1(X0)))) = sK0(X1,k2_relat_1(X0))
    | sK0(X1,k2_relat_1(X0)) = X1
    | k2_tarski(X1,X1) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_363,c_355])).

cnf(c_3638,plain,
    ( k1_funct_1(sK6,sK4(sK6,sK0(X0,k2_relat_1(sK6)))) = sK0(X0,k2_relat_1(sK6))
    | sK0(X0,k2_relat_1(sK6)) = X0
    | k2_tarski(X0,X0) = k2_relat_1(sK6)
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_353,c_1032])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_14283,plain,
    ( k2_tarski(X0,X0) = k2_relat_1(sK6)
    | sK0(X0,k2_relat_1(sK6)) = X0
    | k1_funct_1(sK6,sK4(sK6,sK0(X0,k2_relat_1(sK6)))) = sK0(X0,k2_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3638,c_15])).

cnf(c_14284,plain,
    ( k1_funct_1(sK6,sK4(sK6,sK0(X0,k2_relat_1(sK6)))) = sK0(X0,k2_relat_1(sK6))
    | sK0(X0,k2_relat_1(sK6)) = X0
    | k2_tarski(X0,X0) = k2_relat_1(sK6) ),
    inference(renaming,[status(thm)],[c_14283])).

cnf(c_11,negated_conjecture,
    ( k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_14325,plain,
    ( k1_funct_1(sK6,sK4(sK6,sK0(k1_funct_1(sK6,sK5),k2_relat_1(sK6)))) = sK0(k1_funct_1(sK6,sK5),k2_relat_1(sK6))
    | sK0(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = k1_funct_1(sK6,sK5) ),
    inference(superposition,[status(thm)],[c_14284,c_11])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_354,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12,negated_conjecture,
    ( k2_tarski(sK5,sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_361,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_704,plain,
    ( sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_361])).

cnf(c_846,plain,
    ( sK4(sK6,X0) = sK5
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_354,c_704])).

cnf(c_16,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2129,plain,
    ( sK4(sK6,X0) = sK5
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_846,c_15,c_16])).

cnf(c_2137,plain,
    ( sK4(sK6,sK0(X0,k2_relat_1(sK6))) = sK5
    | sK0(X0,k2_relat_1(sK6)) = X0
    | k2_tarski(X0,X0) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_363,c_2129])).

cnf(c_2653,plain,
    ( sK4(sK6,sK0(k1_funct_1(sK6,sK5),k2_relat_1(sK6))) = sK5
    | sK0(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = k1_funct_1(sK6,sK5) ),
    inference(superposition,[status(thm)],[c_2137,c_11])).

cnf(c_14297,plain,
    ( sK0(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = k1_funct_1(sK6,sK5)
    | k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2653,c_14284])).

cnf(c_15107,plain,
    ( sK0(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = k1_funct_1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14325,c_11,c_14297])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | sK0(X0,X1) != X0
    | k2_tarski(X0,X0) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_364,plain,
    ( sK0(X0,X1) != X0
    | k2_tarski(X0,X0) = X1
    | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_15112,plain,
    ( k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
    | r2_hidden(sK0(k1_funct_1(sK6,sK5),k2_relat_1(sK6)),k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15107,c_364])).

cnf(c_15119,plain,
    ( k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
    | r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15112,c_15107])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5450,plain,
    ( r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6))
    | ~ r2_hidden(sK5,k1_relat_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5452,plain,
    ( r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5450])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_362,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_597,plain,
    ( r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_362])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15119,c_5452,c_597,c_11,c_16,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.83/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/0.98  
% 3.83/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.83/0.98  
% 3.83/0.98  ------  iProver source info
% 3.83/0.98  
% 3.83/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.83/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.83/0.98  git: non_committed_changes: false
% 3.83/0.98  git: last_make_outside_of_git: false
% 3.83/0.98  
% 3.83/0.98  ------ 
% 3.83/0.98  
% 3.83/0.98  ------ Input Options
% 3.83/0.98  
% 3.83/0.98  --out_options                           all
% 3.83/0.98  --tptp_safe_out                         true
% 3.83/0.98  --problem_path                          ""
% 3.83/0.98  --include_path                          ""
% 3.83/0.98  --clausifier                            res/vclausify_rel
% 3.83/0.98  --clausifier_options                    --mode clausify
% 3.83/0.98  --stdin                                 false
% 3.83/0.98  --stats_out                             sel
% 3.83/0.98  
% 3.83/0.98  ------ General Options
% 3.83/0.98  
% 3.83/0.98  --fof                                   false
% 3.83/0.98  --time_out_real                         604.99
% 3.83/0.98  --time_out_virtual                      -1.
% 3.83/0.98  --symbol_type_check                     false
% 3.83/0.98  --clausify_out                          false
% 3.83/0.98  --sig_cnt_out                           false
% 3.83/0.98  --trig_cnt_out                          false
% 3.83/0.98  --trig_cnt_out_tolerance                1.
% 3.83/0.98  --trig_cnt_out_sk_spl                   false
% 3.83/0.98  --abstr_cl_out                          false
% 3.83/0.98  
% 3.83/0.98  ------ Global Options
% 3.83/0.98  
% 3.83/0.98  --schedule                              none
% 3.83/0.98  --add_important_lit                     false
% 3.83/0.98  --prop_solver_per_cl                    1000
% 3.83/0.98  --min_unsat_core                        false
% 3.83/0.98  --soft_assumptions                      false
% 3.83/0.98  --soft_lemma_size                       3
% 3.83/0.98  --prop_impl_unit_size                   0
% 3.83/0.98  --prop_impl_unit                        []
% 3.83/0.98  --share_sel_clauses                     true
% 3.83/0.98  --reset_solvers                         false
% 3.83/0.98  --bc_imp_inh                            [conj_cone]
% 3.83/0.98  --conj_cone_tolerance                   3.
% 3.83/0.98  --extra_neg_conj                        none
% 3.83/0.98  --large_theory_mode                     true
% 3.83/0.98  --prolific_symb_bound                   200
% 3.83/0.98  --lt_threshold                          2000
% 3.83/0.98  --clause_weak_htbl                      true
% 3.83/0.98  --gc_record_bc_elim                     false
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing Options
% 3.83/0.99  
% 3.83/0.99  --preprocessing_flag                    true
% 3.83/0.99  --time_out_prep_mult                    0.1
% 3.83/0.99  --splitting_mode                        input
% 3.83/0.99  --splitting_grd                         true
% 3.83/0.99  --splitting_cvd                         false
% 3.83/0.99  --splitting_cvd_svl                     false
% 3.83/0.99  --splitting_nvd                         32
% 3.83/0.99  --sub_typing                            true
% 3.83/0.99  --prep_gs_sim                           false
% 3.83/0.99  --prep_unflatten                        true
% 3.83/0.99  --prep_res_sim                          true
% 3.83/0.99  --prep_upred                            true
% 3.83/0.99  --prep_sem_filter                       exhaustive
% 3.83/0.99  --prep_sem_filter_out                   false
% 3.83/0.99  --pred_elim                             false
% 3.83/0.99  --res_sim_input                         true
% 3.83/0.99  --eq_ax_congr_red                       true
% 3.83/0.99  --pure_diseq_elim                       true
% 3.83/0.99  --brand_transform                       false
% 3.83/0.99  --non_eq_to_eq                          false
% 3.83/0.99  --prep_def_merge                        true
% 3.83/0.99  --prep_def_merge_prop_impl              false
% 3.83/0.99  --prep_def_merge_mbd                    true
% 3.83/0.99  --prep_def_merge_tr_red                 false
% 3.83/0.99  --prep_def_merge_tr_cl                  false
% 3.83/0.99  --smt_preprocessing                     true
% 3.83/0.99  --smt_ac_axioms                         fast
% 3.83/0.99  --preprocessed_out                      false
% 3.83/0.99  --preprocessed_stats                    false
% 3.83/0.99  
% 3.83/0.99  ------ Abstraction refinement Options
% 3.83/0.99  
% 3.83/0.99  --abstr_ref                             []
% 3.83/0.99  --abstr_ref_prep                        false
% 3.83/0.99  --abstr_ref_until_sat                   false
% 3.83/0.99  --abstr_ref_sig_restrict                funpre
% 3.83/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/0.99  --abstr_ref_under                       []
% 3.83/0.99  
% 3.83/0.99  ------ SAT Options
% 3.83/0.99  
% 3.83/0.99  --sat_mode                              false
% 3.83/0.99  --sat_fm_restart_options                ""
% 3.83/0.99  --sat_gr_def                            false
% 3.83/0.99  --sat_epr_types                         true
% 3.83/0.99  --sat_non_cyclic_types                  false
% 3.83/0.99  --sat_finite_models                     false
% 3.83/0.99  --sat_fm_lemmas                         false
% 3.83/0.99  --sat_fm_prep                           false
% 3.83/0.99  --sat_fm_uc_incr                        true
% 3.83/0.99  --sat_out_model                         small
% 3.83/0.99  --sat_out_clauses                       false
% 3.83/0.99  
% 3.83/0.99  ------ QBF Options
% 3.83/0.99  
% 3.83/0.99  --qbf_mode                              false
% 3.83/0.99  --qbf_elim_univ                         false
% 3.83/0.99  --qbf_dom_inst                          none
% 3.83/0.99  --qbf_dom_pre_inst                      false
% 3.83/0.99  --qbf_sk_in                             false
% 3.83/0.99  --qbf_pred_elim                         true
% 3.83/0.99  --qbf_split                             512
% 3.83/0.99  
% 3.83/0.99  ------ BMC1 Options
% 3.83/0.99  
% 3.83/0.99  --bmc1_incremental                      false
% 3.83/0.99  --bmc1_axioms                           reachable_all
% 3.83/0.99  --bmc1_min_bound                        0
% 3.83/0.99  --bmc1_max_bound                        -1
% 3.83/0.99  --bmc1_max_bound_default                -1
% 3.83/0.99  --bmc1_symbol_reachability              true
% 3.83/0.99  --bmc1_property_lemmas                  false
% 3.83/0.99  --bmc1_k_induction                      false
% 3.83/0.99  --bmc1_non_equiv_states                 false
% 3.83/0.99  --bmc1_deadlock                         false
% 3.83/0.99  --bmc1_ucm                              false
% 3.83/0.99  --bmc1_add_unsat_core                   none
% 3.83/0.99  --bmc1_unsat_core_children              false
% 3.83/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/0.99  --bmc1_out_stat                         full
% 3.83/0.99  --bmc1_ground_init                      false
% 3.83/0.99  --bmc1_pre_inst_next_state              false
% 3.83/0.99  --bmc1_pre_inst_state                   false
% 3.83/0.99  --bmc1_pre_inst_reach_state             false
% 3.83/0.99  --bmc1_out_unsat_core                   false
% 3.83/0.99  --bmc1_aig_witness_out                  false
% 3.83/0.99  --bmc1_verbose                          false
% 3.83/0.99  --bmc1_dump_clauses_tptp                false
% 3.83/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.83/0.99  --bmc1_dump_file                        -
% 3.83/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.83/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.83/0.99  --bmc1_ucm_extend_mode                  1
% 3.83/0.99  --bmc1_ucm_init_mode                    2
% 3.83/0.99  --bmc1_ucm_cone_mode                    none
% 3.83/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.83/0.99  --bmc1_ucm_relax_model                  4
% 3.83/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.83/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/0.99  --bmc1_ucm_layered_model                none
% 3.83/0.99  --bmc1_ucm_max_lemma_size               10
% 3.83/0.99  
% 3.83/0.99  ------ AIG Options
% 3.83/0.99  
% 3.83/0.99  --aig_mode                              false
% 3.83/0.99  
% 3.83/0.99  ------ Instantiation Options
% 3.83/0.99  
% 3.83/0.99  --instantiation_flag                    true
% 3.83/0.99  --inst_sos_flag                         false
% 3.83/0.99  --inst_sos_phase                        true
% 3.83/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/0.99  --inst_lit_sel_side                     num_symb
% 3.83/0.99  --inst_solver_per_active                1400
% 3.83/0.99  --inst_solver_calls_frac                1.
% 3.83/0.99  --inst_passive_queue_type               priority_queues
% 3.83/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/0.99  --inst_passive_queues_freq              [25;2]
% 3.83/0.99  --inst_dismatching                      true
% 3.83/0.99  --inst_eager_unprocessed_to_passive     true
% 3.83/0.99  --inst_prop_sim_given                   true
% 3.83/0.99  --inst_prop_sim_new                     false
% 3.83/0.99  --inst_subs_new                         false
% 3.83/0.99  --inst_eq_res_simp                      false
% 3.83/0.99  --inst_subs_given                       false
% 3.83/0.99  --inst_orphan_elimination               true
% 3.83/0.99  --inst_learning_loop_flag               true
% 3.83/0.99  --inst_learning_start                   3000
% 3.83/0.99  --inst_learning_factor                  2
% 3.83/0.99  --inst_start_prop_sim_after_learn       3
% 3.83/0.99  --inst_sel_renew                        solver
% 3.83/0.99  --inst_lit_activity_flag                true
% 3.83/0.99  --inst_restr_to_given                   false
% 3.83/0.99  --inst_activity_threshold               500
% 3.83/0.99  --inst_out_proof                        true
% 3.83/0.99  
% 3.83/0.99  ------ Resolution Options
% 3.83/0.99  
% 3.83/0.99  --resolution_flag                       true
% 3.83/0.99  --res_lit_sel                           adaptive
% 3.83/0.99  --res_lit_sel_side                      none
% 3.83/0.99  --res_ordering                          kbo
% 3.83/0.99  --res_to_prop_solver                    active
% 3.83/0.99  --res_prop_simpl_new                    false
% 3.83/0.99  --res_prop_simpl_given                  true
% 3.83/0.99  --res_passive_queue_type                priority_queues
% 3.83/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/0.99  --res_passive_queues_freq               [15;5]
% 3.83/0.99  --res_forward_subs                      full
% 3.83/0.99  --res_backward_subs                     full
% 3.83/0.99  --res_forward_subs_resolution           true
% 3.83/0.99  --res_backward_subs_resolution          true
% 3.83/0.99  --res_orphan_elimination                true
% 3.83/0.99  --res_time_limit                        2.
% 3.83/0.99  --res_out_proof                         true
% 3.83/0.99  
% 3.83/0.99  ------ Superposition Options
% 3.83/0.99  
% 3.83/0.99  --superposition_flag                    true
% 3.83/0.99  --sup_passive_queue_type                priority_queues
% 3.83/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/0.99  --sup_passive_queues_freq               [1;4]
% 3.83/0.99  --demod_completeness_check              fast
% 3.83/0.99  --demod_use_ground                      true
% 3.83/0.99  --sup_to_prop_solver                    passive
% 3.83/0.99  --sup_prop_simpl_new                    true
% 3.83/0.99  --sup_prop_simpl_given                  true
% 3.83/0.99  --sup_fun_splitting                     false
% 3.83/0.99  --sup_smt_interval                      50000
% 3.83/0.99  
% 3.83/0.99  ------ Superposition Simplification Setup
% 3.83/0.99  
% 3.83/0.99  --sup_indices_passive                   []
% 3.83/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_full_bw                           [BwDemod]
% 3.83/0.99  --sup_immed_triv                        [TrivRules]
% 3.83/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_immed_bw_main                     []
% 3.83/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.83/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.83/0.99  
% 3.83/0.99  ------ Combination Options
% 3.83/0.99  
% 3.83/0.99  --comb_res_mult                         3
% 3.83/0.99  --comb_sup_mult                         2
% 3.83/0.99  --comb_inst_mult                        10
% 3.83/0.99  
% 3.83/0.99  ------ Debug Options
% 3.83/0.99  
% 3.83/0.99  --dbg_backtrace                         false
% 3.83/0.99  --dbg_dump_prop_clauses                 false
% 3.83/0.99  --dbg_dump_prop_clauses_file            -
% 3.83/0.99  --dbg_out_stat                          false
% 3.83/0.99  ------ Parsing...
% 3.83/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.83/0.99  ------ Proving...
% 3.83/0.99  ------ Problem Properties 
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  clauses                                 15
% 3.83/0.99  conjectures                             4
% 3.83/0.99  EPR                                     2
% 3.83/0.99  Horn                                    12
% 3.83/0.99  unary                                   5
% 3.83/0.99  binary                                  1
% 3.83/0.99  lits                                    44
% 3.83/0.99  lits eq                                 13
% 3.83/0.99  fd_pure                                 0
% 3.83/0.99  fd_pseudo                               0
% 3.83/0.99  fd_cond                                 0
% 3.83/0.99  fd_pseudo_cond                          5
% 3.83/0.99  AC symbols                              0
% 3.83/0.99  
% 3.83/0.99  ------ Input Options Time Limit: Unbounded
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  ------ 
% 3.83/0.99  Current options:
% 3.83/0.99  ------ 
% 3.83/0.99  
% 3.83/0.99  ------ Input Options
% 3.83/0.99  
% 3.83/0.99  --out_options                           all
% 3.83/0.99  --tptp_safe_out                         true
% 3.83/0.99  --problem_path                          ""
% 3.83/0.99  --include_path                          ""
% 3.83/0.99  --clausifier                            res/vclausify_rel
% 3.83/0.99  --clausifier_options                    --mode clausify
% 3.83/0.99  --stdin                                 false
% 3.83/0.99  --stats_out                             sel
% 3.83/0.99  
% 3.83/0.99  ------ General Options
% 3.83/0.99  
% 3.83/0.99  --fof                                   false
% 3.83/0.99  --time_out_real                         604.99
% 3.83/0.99  --time_out_virtual                      -1.
% 3.83/0.99  --symbol_type_check                     false
% 3.83/0.99  --clausify_out                          false
% 3.83/0.99  --sig_cnt_out                           false
% 3.83/0.99  --trig_cnt_out                          false
% 3.83/0.99  --trig_cnt_out_tolerance                1.
% 3.83/0.99  --trig_cnt_out_sk_spl                   false
% 3.83/0.99  --abstr_cl_out                          false
% 3.83/0.99  
% 3.83/0.99  ------ Global Options
% 3.83/0.99  
% 3.83/0.99  --schedule                              none
% 3.83/0.99  --add_important_lit                     false
% 3.83/0.99  --prop_solver_per_cl                    1000
% 3.83/0.99  --min_unsat_core                        false
% 3.83/0.99  --soft_assumptions                      false
% 3.83/0.99  --soft_lemma_size                       3
% 3.83/0.99  --prop_impl_unit_size                   0
% 3.83/0.99  --prop_impl_unit                        []
% 3.83/0.99  --share_sel_clauses                     true
% 3.83/0.99  --reset_solvers                         false
% 3.83/0.99  --bc_imp_inh                            [conj_cone]
% 3.83/0.99  --conj_cone_tolerance                   3.
% 3.83/0.99  --extra_neg_conj                        none
% 3.83/0.99  --large_theory_mode                     true
% 3.83/0.99  --prolific_symb_bound                   200
% 3.83/0.99  --lt_threshold                          2000
% 3.83/0.99  --clause_weak_htbl                      true
% 3.83/0.99  --gc_record_bc_elim                     false
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing Options
% 3.83/0.99  
% 3.83/0.99  --preprocessing_flag                    true
% 3.83/0.99  --time_out_prep_mult                    0.1
% 3.83/0.99  --splitting_mode                        input
% 3.83/0.99  --splitting_grd                         true
% 3.83/0.99  --splitting_cvd                         false
% 3.83/0.99  --splitting_cvd_svl                     false
% 3.83/0.99  --splitting_nvd                         32
% 3.83/0.99  --sub_typing                            true
% 3.83/0.99  --prep_gs_sim                           false
% 3.83/0.99  --prep_unflatten                        true
% 3.83/0.99  --prep_res_sim                          true
% 3.83/0.99  --prep_upred                            true
% 3.83/0.99  --prep_sem_filter                       exhaustive
% 3.83/0.99  --prep_sem_filter_out                   false
% 3.83/0.99  --pred_elim                             false
% 3.83/0.99  --res_sim_input                         true
% 3.83/0.99  --eq_ax_congr_red                       true
% 3.83/0.99  --pure_diseq_elim                       true
% 3.83/0.99  --brand_transform                       false
% 3.83/0.99  --non_eq_to_eq                          false
% 3.83/0.99  --prep_def_merge                        true
% 3.83/0.99  --prep_def_merge_prop_impl              false
% 3.83/0.99  --prep_def_merge_mbd                    true
% 3.83/0.99  --prep_def_merge_tr_red                 false
% 3.83/0.99  --prep_def_merge_tr_cl                  false
% 3.83/0.99  --smt_preprocessing                     true
% 3.83/0.99  --smt_ac_axioms                         fast
% 3.83/0.99  --preprocessed_out                      false
% 3.83/0.99  --preprocessed_stats                    false
% 3.83/0.99  
% 3.83/0.99  ------ Abstraction refinement Options
% 3.83/0.99  
% 3.83/0.99  --abstr_ref                             []
% 3.83/0.99  --abstr_ref_prep                        false
% 3.83/0.99  --abstr_ref_until_sat                   false
% 3.83/0.99  --abstr_ref_sig_restrict                funpre
% 3.83/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/0.99  --abstr_ref_under                       []
% 3.83/0.99  
% 3.83/0.99  ------ SAT Options
% 3.83/0.99  
% 3.83/0.99  --sat_mode                              false
% 3.83/0.99  --sat_fm_restart_options                ""
% 3.83/0.99  --sat_gr_def                            false
% 3.83/0.99  --sat_epr_types                         true
% 3.83/0.99  --sat_non_cyclic_types                  false
% 3.83/0.99  --sat_finite_models                     false
% 3.83/0.99  --sat_fm_lemmas                         false
% 3.83/0.99  --sat_fm_prep                           false
% 3.83/0.99  --sat_fm_uc_incr                        true
% 3.83/0.99  --sat_out_model                         small
% 3.83/0.99  --sat_out_clauses                       false
% 3.83/0.99  
% 3.83/0.99  ------ QBF Options
% 3.83/0.99  
% 3.83/0.99  --qbf_mode                              false
% 3.83/0.99  --qbf_elim_univ                         false
% 3.83/0.99  --qbf_dom_inst                          none
% 3.83/0.99  --qbf_dom_pre_inst                      false
% 3.83/0.99  --qbf_sk_in                             false
% 3.83/0.99  --qbf_pred_elim                         true
% 3.83/0.99  --qbf_split                             512
% 3.83/0.99  
% 3.83/0.99  ------ BMC1 Options
% 3.83/0.99  
% 3.83/0.99  --bmc1_incremental                      false
% 3.83/0.99  --bmc1_axioms                           reachable_all
% 3.83/0.99  --bmc1_min_bound                        0
% 3.83/0.99  --bmc1_max_bound                        -1
% 3.83/0.99  --bmc1_max_bound_default                -1
% 3.83/0.99  --bmc1_symbol_reachability              true
% 3.83/0.99  --bmc1_property_lemmas                  false
% 3.83/0.99  --bmc1_k_induction                      false
% 3.83/0.99  --bmc1_non_equiv_states                 false
% 3.83/0.99  --bmc1_deadlock                         false
% 3.83/0.99  --bmc1_ucm                              false
% 3.83/0.99  --bmc1_add_unsat_core                   none
% 3.83/0.99  --bmc1_unsat_core_children              false
% 3.83/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/0.99  --bmc1_out_stat                         full
% 3.83/0.99  --bmc1_ground_init                      false
% 3.83/0.99  --bmc1_pre_inst_next_state              false
% 3.83/0.99  --bmc1_pre_inst_state                   false
% 3.83/0.99  --bmc1_pre_inst_reach_state             false
% 3.83/0.99  --bmc1_out_unsat_core                   false
% 3.83/0.99  --bmc1_aig_witness_out                  false
% 3.83/0.99  --bmc1_verbose                          false
% 3.83/0.99  --bmc1_dump_clauses_tptp                false
% 3.83/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.83/0.99  --bmc1_dump_file                        -
% 3.83/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.83/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.83/0.99  --bmc1_ucm_extend_mode                  1
% 3.83/0.99  --bmc1_ucm_init_mode                    2
% 3.83/0.99  --bmc1_ucm_cone_mode                    none
% 3.83/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.83/0.99  --bmc1_ucm_relax_model                  4
% 3.83/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.83/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/0.99  --bmc1_ucm_layered_model                none
% 3.83/0.99  --bmc1_ucm_max_lemma_size               10
% 3.83/0.99  
% 3.83/0.99  ------ AIG Options
% 3.83/0.99  
% 3.83/0.99  --aig_mode                              false
% 3.83/0.99  
% 3.83/0.99  ------ Instantiation Options
% 3.83/0.99  
% 3.83/0.99  --instantiation_flag                    true
% 3.83/0.99  --inst_sos_flag                         false
% 3.83/0.99  --inst_sos_phase                        true
% 3.83/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/0.99  --inst_lit_sel_side                     num_symb
% 3.83/0.99  --inst_solver_per_active                1400
% 3.83/0.99  --inst_solver_calls_frac                1.
% 3.83/0.99  --inst_passive_queue_type               priority_queues
% 3.83/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/0.99  --inst_passive_queues_freq              [25;2]
% 3.83/0.99  --inst_dismatching                      true
% 3.83/0.99  --inst_eager_unprocessed_to_passive     true
% 3.83/0.99  --inst_prop_sim_given                   true
% 3.83/0.99  --inst_prop_sim_new                     false
% 3.83/0.99  --inst_subs_new                         false
% 3.83/0.99  --inst_eq_res_simp                      false
% 3.83/0.99  --inst_subs_given                       false
% 3.83/0.99  --inst_orphan_elimination               true
% 3.83/0.99  --inst_learning_loop_flag               true
% 3.83/0.99  --inst_learning_start                   3000
% 3.83/0.99  --inst_learning_factor                  2
% 3.83/0.99  --inst_start_prop_sim_after_learn       3
% 3.83/0.99  --inst_sel_renew                        solver
% 3.83/0.99  --inst_lit_activity_flag                true
% 3.83/0.99  --inst_restr_to_given                   false
% 3.83/0.99  --inst_activity_threshold               500
% 3.83/0.99  --inst_out_proof                        true
% 3.83/0.99  
% 3.83/0.99  ------ Resolution Options
% 3.83/0.99  
% 3.83/0.99  --resolution_flag                       true
% 3.83/0.99  --res_lit_sel                           adaptive
% 3.83/0.99  --res_lit_sel_side                      none
% 3.83/0.99  --res_ordering                          kbo
% 3.83/0.99  --res_to_prop_solver                    active
% 3.83/0.99  --res_prop_simpl_new                    false
% 3.83/0.99  --res_prop_simpl_given                  true
% 3.83/0.99  --res_passive_queue_type                priority_queues
% 3.83/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/0.99  --res_passive_queues_freq               [15;5]
% 3.83/0.99  --res_forward_subs                      full
% 3.83/0.99  --res_backward_subs                     full
% 3.83/0.99  --res_forward_subs_resolution           true
% 3.83/0.99  --res_backward_subs_resolution          true
% 3.83/0.99  --res_orphan_elimination                true
% 3.83/0.99  --res_time_limit                        2.
% 3.83/0.99  --res_out_proof                         true
% 3.83/0.99  
% 3.83/0.99  ------ Superposition Options
% 3.83/0.99  
% 3.83/0.99  --superposition_flag                    true
% 3.83/0.99  --sup_passive_queue_type                priority_queues
% 3.83/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/0.99  --sup_passive_queues_freq               [1;4]
% 3.83/0.99  --demod_completeness_check              fast
% 3.83/0.99  --demod_use_ground                      true
% 3.83/0.99  --sup_to_prop_solver                    passive
% 3.83/0.99  --sup_prop_simpl_new                    true
% 3.83/0.99  --sup_prop_simpl_given                  true
% 3.83/0.99  --sup_fun_splitting                     false
% 3.83/0.99  --sup_smt_interval                      50000
% 3.83/0.99  
% 3.83/0.99  ------ Superposition Simplification Setup
% 3.83/0.99  
% 3.83/0.99  --sup_indices_passive                   []
% 3.83/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_full_bw                           [BwDemod]
% 3.83/0.99  --sup_immed_triv                        [TrivRules]
% 3.83/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_immed_bw_main                     []
% 3.83/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.83/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.83/0.99  
% 3.83/0.99  ------ Combination Options
% 3.83/0.99  
% 3.83/0.99  --comb_res_mult                         3
% 3.83/0.99  --comb_sup_mult                         2
% 3.83/0.99  --comb_inst_mult                        10
% 3.83/0.99  
% 3.83/0.99  ------ Debug Options
% 3.83/0.99  
% 3.83/0.99  --dbg_backtrace                         false
% 3.83/0.99  --dbg_dump_prop_clauses                 false
% 3.83/0.99  --dbg_dump_prop_clauses_file            -
% 3.83/0.99  --dbg_out_stat                          false
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  ------ Proving...
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  % SZS status Theorem for theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  fof(f5,conjecture,(
% 3.83/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f6,negated_conjecture,(
% 3.83/0.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.83/0.99    inference(negated_conjecture,[],[f5])).
% 3.83/0.99  
% 3.83/0.99  fof(f11,plain,(
% 3.83/0.99    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.83/0.99    inference(ennf_transformation,[],[f6])).
% 3.83/0.99  
% 3.83/0.99  fof(f12,plain,(
% 3.83/0.99    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.83/0.99    inference(flattening,[],[f11])).
% 3.83/0.99  
% 3.83/0.99  fof(f25,plain,(
% 3.83/0.99    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f26,plain,(
% 3.83/0.99    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 3.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f12,f25])).
% 3.83/0.99  
% 3.83/0.99  fof(f40,plain,(
% 3.83/0.99    v1_funct_1(sK6)),
% 3.83/0.99    inference(cnf_transformation,[],[f26])).
% 3.83/0.99  
% 3.83/0.99  fof(f1,axiom,(
% 3.83/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f13,plain,(
% 3.83/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.83/0.99    inference(nnf_transformation,[],[f1])).
% 3.83/0.99  
% 3.83/0.99  fof(f14,plain,(
% 3.83/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.83/0.99    inference(rectify,[],[f13])).
% 3.83/0.99  
% 3.83/0.99  fof(f15,plain,(
% 3.83/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f16,plain,(
% 3.83/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 3.83/0.99  
% 3.83/0.99  fof(f29,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f16])).
% 3.83/0.99  
% 3.83/0.99  fof(f2,axiom,(
% 3.83/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f31,plain,(
% 3.83/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f2])).
% 3.83/0.99  
% 3.83/0.99  fof(f44,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k2_tarski(X0,X0) = X1 | sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)) )),
% 3.83/0.99    inference(definition_unfolding,[],[f29,f31])).
% 3.83/0.99  
% 3.83/0.99  fof(f4,axiom,(
% 3.83/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f9,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.83/0.99    inference(ennf_transformation,[],[f4])).
% 3.83/0.99  
% 3.83/0.99  fof(f10,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.83/0.99    inference(flattening,[],[f9])).
% 3.83/0.99  
% 3.83/0.99  fof(f19,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.83/0.99    inference(nnf_transformation,[],[f10])).
% 3.83/0.99  
% 3.83/0.99  fof(f20,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.83/0.99    inference(rectify,[],[f19])).
% 3.83/0.99  
% 3.83/0.99  fof(f23,plain,(
% 3.83/0.99    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f22,plain,(
% 3.83/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f21,plain,(
% 3.83/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f24,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f23,f22,f21])).
% 3.83/0.99  
% 3.83/0.99  fof(f34,plain,(
% 3.83/0.99    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f24])).
% 3.83/0.99  
% 3.83/0.99  fof(f54,plain,(
% 3.83/0.99    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.83/0.99    inference(equality_resolution,[],[f34])).
% 3.83/0.99  
% 3.83/0.99  fof(f39,plain,(
% 3.83/0.99    v1_relat_1(sK6)),
% 3.83/0.99    inference(cnf_transformation,[],[f26])).
% 3.83/0.99  
% 3.83/0.99  fof(f42,plain,(
% 3.83/0.99    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)),
% 3.83/0.99    inference(cnf_transformation,[],[f26])).
% 3.83/0.99  
% 3.83/0.99  fof(f47,plain,(
% 3.83/0.99    k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)),
% 3.83/0.99    inference(definition_unfolding,[],[f42,f31])).
% 3.83/0.99  
% 3.83/0.99  fof(f33,plain,(
% 3.83/0.99    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f24])).
% 3.83/0.99  
% 3.83/0.99  fof(f55,plain,(
% 3.83/0.99    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.83/0.99    inference(equality_resolution,[],[f33])).
% 3.83/0.99  
% 3.83/0.99  fof(f41,plain,(
% 3.83/0.99    k1_tarski(sK5) = k1_relat_1(sK6)),
% 3.83/0.99    inference(cnf_transformation,[],[f26])).
% 3.83/0.99  
% 3.83/0.99  fof(f48,plain,(
% 3.83/0.99    k2_tarski(sK5,sK5) = k1_relat_1(sK6)),
% 3.83/0.99    inference(definition_unfolding,[],[f41,f31])).
% 3.83/0.99  
% 3.83/0.99  fof(f27,plain,(
% 3.83/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.83/0.99    inference(cnf_transformation,[],[f16])).
% 3.83/0.99  
% 3.83/0.99  fof(f46,plain,(
% 3.83/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 3.83/0.99    inference(definition_unfolding,[],[f27,f31])).
% 3.83/0.99  
% 3.83/0.99  fof(f51,plain,(
% 3.83/0.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 3.83/0.99    inference(equality_resolution,[],[f46])).
% 3.83/0.99  
% 3.83/0.99  fof(f30,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f16])).
% 3.83/0.99  
% 3.83/0.99  fof(f43,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k2_tarski(X0,X0) = X1 | sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.83/0.99    inference(definition_unfolding,[],[f30,f31])).
% 3.83/0.99  
% 3.83/0.99  fof(f35,plain,(
% 3.83/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f24])).
% 3.83/0.99  
% 3.83/0.99  fof(f52,plain,(
% 3.83/0.99    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.83/0.99    inference(equality_resolution,[],[f35])).
% 3.83/0.99  
% 3.83/0.99  fof(f53,plain,(
% 3.83/0.99    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.83/0.99    inference(equality_resolution,[],[f52])).
% 3.83/0.99  
% 3.83/0.99  fof(f28,plain,(
% 3.83/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.83/0.99    inference(cnf_transformation,[],[f16])).
% 3.83/0.99  
% 3.83/0.99  fof(f45,plain,(
% 3.83/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 3.83/0.99    inference(definition_unfolding,[],[f28,f31])).
% 3.83/0.99  
% 3.83/0.99  fof(f49,plain,(
% 3.83/0.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 3.83/0.99    inference(equality_resolution,[],[f45])).
% 3.83/0.99  
% 3.83/0.99  fof(f50,plain,(
% 3.83/0.99    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 3.83/0.99    inference(equality_resolution,[],[f49])).
% 3.83/0.99  
% 3.83/0.99  cnf(c_13,negated_conjecture,
% 3.83/0.99      ( v1_funct_1(sK6) ),
% 3.83/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_353,plain,
% 3.83/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1,plain,
% 3.83/0.99      ( r2_hidden(sK0(X0,X1),X1)
% 3.83/0.99      | sK0(X0,X1) = X0
% 3.83/0.99      | k2_tarski(X0,X0) = X1 ),
% 3.83/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_363,plain,
% 3.83/0.99      ( sK0(X0,X1) = X0
% 3.83/0.99      | k2_tarski(X0,X0) = X1
% 3.83/0.99      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_9,plain,
% 3.83/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.83/0.99      | ~ v1_funct_1(X1)
% 3.83/0.99      | ~ v1_relat_1(X1)
% 3.83/0.99      | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
% 3.83/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_355,plain,
% 3.83/0.99      ( k1_funct_1(X0,sK4(X0,X1)) = X1
% 3.83/0.99      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.83/0.99      | v1_funct_1(X0) != iProver_top
% 3.83/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1032,plain,
% 3.83/0.99      ( k1_funct_1(X0,sK4(X0,sK0(X1,k2_relat_1(X0)))) = sK0(X1,k2_relat_1(X0))
% 3.83/0.99      | sK0(X1,k2_relat_1(X0)) = X1
% 3.83/0.99      | k2_tarski(X1,X1) = k2_relat_1(X0)
% 3.83/0.99      | v1_funct_1(X0) != iProver_top
% 3.83/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_363,c_355]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_3638,plain,
% 3.83/0.99      ( k1_funct_1(sK6,sK4(sK6,sK0(X0,k2_relat_1(sK6)))) = sK0(X0,k2_relat_1(sK6))
% 3.83/0.99      | sK0(X0,k2_relat_1(sK6)) = X0
% 3.83/0.99      | k2_tarski(X0,X0) = k2_relat_1(sK6)
% 3.83/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_353,c_1032]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_14,negated_conjecture,
% 3.83/0.99      ( v1_relat_1(sK6) ),
% 3.83/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_15,plain,
% 3.83/0.99      ( v1_relat_1(sK6) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_14283,plain,
% 3.83/0.99      ( k2_tarski(X0,X0) = k2_relat_1(sK6)
% 3.83/0.99      | sK0(X0,k2_relat_1(sK6)) = X0
% 3.83/0.99      | k1_funct_1(sK6,sK4(sK6,sK0(X0,k2_relat_1(sK6)))) = sK0(X0,k2_relat_1(sK6)) ),
% 3.83/0.99      inference(global_propositional_subsumption,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_3638,c_15]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_14284,plain,
% 3.83/0.99      ( k1_funct_1(sK6,sK4(sK6,sK0(X0,k2_relat_1(sK6)))) = sK0(X0,k2_relat_1(sK6))
% 3.83/0.99      | sK0(X0,k2_relat_1(sK6)) = X0
% 3.83/0.99      | k2_tarski(X0,X0) = k2_relat_1(sK6) ),
% 3.83/0.99      inference(renaming,[status(thm)],[c_14283]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_11,negated_conjecture,
% 3.83/0.99      ( k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
% 3.83/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_14325,plain,
% 3.83/0.99      ( k1_funct_1(sK6,sK4(sK6,sK0(k1_funct_1(sK6,sK5),k2_relat_1(sK6)))) = sK0(k1_funct_1(sK6,sK5),k2_relat_1(sK6))
% 3.83/0.99      | sK0(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = k1_funct_1(sK6,sK5) ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_14284,c_11]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_10,plain,
% 3.83/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.83/0.99      | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
% 3.83/0.99      | ~ v1_funct_1(X1)
% 3.83/0.99      | ~ v1_relat_1(X1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_354,plain,
% 3.83/0.99      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.83/0.99      | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.83/0.99      | v1_funct_1(X1) != iProver_top
% 3.83/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_12,negated_conjecture,
% 3.83/0.99      ( k2_tarski(sK5,sK5) = k1_relat_1(sK6) ),
% 3.83/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_3,plain,
% 3.83/0.99      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 3.83/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_361,plain,
% 3.83/0.99      ( X0 = X1 | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_704,plain,
% 3.83/0.99      ( sK5 = X0 | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_12,c_361]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_846,plain,
% 3.83/0.99      ( sK4(sK6,X0) = sK5
% 3.83/0.99      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.83/0.99      | v1_funct_1(sK6) != iProver_top
% 3.83/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_354,c_704]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_16,plain,
% 3.83/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2129,plain,
% 3.83/0.99      ( sK4(sK6,X0) = sK5
% 3.83/0.99      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 3.83/0.99      inference(global_propositional_subsumption,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_846,c_15,c_16]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2137,plain,
% 3.83/0.99      ( sK4(sK6,sK0(X0,k2_relat_1(sK6))) = sK5
% 3.83/0.99      | sK0(X0,k2_relat_1(sK6)) = X0
% 3.83/0.99      | k2_tarski(X0,X0) = k2_relat_1(sK6) ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_363,c_2129]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2653,plain,
% 3.83/0.99      ( sK4(sK6,sK0(k1_funct_1(sK6,sK5),k2_relat_1(sK6))) = sK5
% 3.83/0.99      | sK0(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = k1_funct_1(sK6,sK5) ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_2137,c_11]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_14297,plain,
% 3.83/0.99      ( sK0(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = k1_funct_1(sK6,sK5)
% 3.83/0.99      | k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6) ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_2653,c_14284]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_15107,plain,
% 3.83/0.99      ( sK0(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = k1_funct_1(sK6,sK5) ),
% 3.83/0.99      inference(global_propositional_subsumption,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_14325,c_11,c_14297]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_0,plain,
% 3.83/0.99      ( ~ r2_hidden(sK0(X0,X1),X1)
% 3.83/0.99      | sK0(X0,X1) != X0
% 3.83/0.99      | k2_tarski(X0,X0) = X1 ),
% 3.83/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_364,plain,
% 3.83/0.99      ( sK0(X0,X1) != X0
% 3.83/0.99      | k2_tarski(X0,X0) = X1
% 3.83/0.99      | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_15112,plain,
% 3.83/0.99      ( k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
% 3.83/0.99      | r2_hidden(sK0(k1_funct_1(sK6,sK5),k2_relat_1(sK6)),k2_relat_1(sK6)) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_15107,c_364]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_15119,plain,
% 3.83/0.99      ( k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
% 3.83/0.99      | r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) != iProver_top ),
% 3.83/0.99      inference(light_normalisation,[status(thm)],[c_15112,c_15107]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_8,plain,
% 3.83/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.83/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.83/0.99      | ~ v1_funct_1(X1)
% 3.83/0.99      | ~ v1_relat_1(X1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_5450,plain,
% 3.83/0.99      ( r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6))
% 3.83/0.99      | ~ r2_hidden(sK5,k1_relat_1(sK6))
% 3.83/0.99      | ~ v1_funct_1(sK6)
% 3.83/0.99      | ~ v1_relat_1(sK6) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_5452,plain,
% 3.83/0.99      ( r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 3.83/0.99      | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top
% 3.83/0.99      | v1_funct_1(sK6) != iProver_top
% 3.83/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_5450]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2,plain,
% 3.83/0.99      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 3.83/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_362,plain,
% 3.83/0.99      ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_597,plain,
% 3.83/0.99      ( r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_12,c_362]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(contradiction,plain,
% 3.83/0.99      ( $false ),
% 3.83/0.99      inference(minisat,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_15119,c_5452,c_597,c_11,c_16,c_15]) ).
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  ------                               Statistics
% 3.83/0.99  
% 3.83/0.99  ------ Selected
% 3.83/0.99  
% 3.83/0.99  total_time:                             0.418
% 3.83/0.99  
%------------------------------------------------------------------------------
