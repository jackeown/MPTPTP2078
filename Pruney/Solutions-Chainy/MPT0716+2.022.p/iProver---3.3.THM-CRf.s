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
% DateTime   : Thu Dec  3 11:52:55 EST 2020

% Result     : Theorem 7.17s
% Output     : CNFRefutation 7.17s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 465 expanded)
%              Number of clauses        :   45 ( 119 expanded)
%              Number of leaves         :   11 ( 123 expanded)
%              Depth                    :   17
%              Number of atoms          :  271 (3274 expanded)
%              Number of equality atoms :   72 ( 175 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
            | ~ r1_tarski(X2,k1_relat_1(X0))
            | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
          & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
            | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
     => ( ( ~ r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1))
          | ~ r1_tarski(sK2,k1_relat_1(X0))
          | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1))) )
        & ( ( r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1))
            & r1_tarski(sK2,k1_relat_1(X0)) )
          | r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1))) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1))
              | ~ r1_tarski(X2,k1_relat_1(X0))
              | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1))) )
            & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1))
                & r1_tarski(X2,k1_relat_1(X0)) )
              | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1))) ) )
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  | ~ r1_tarski(X2,k1_relat_1(X0))
                  | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
                & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                    & r1_tarski(X2,k1_relat_1(X0)) )
                  | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(sK0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
              & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(sK0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
      | ~ r1_tarski(sK2,k1_relat_1(sK0))
      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        & r1_tarski(sK2,k1_relat_1(sK0)) )
      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25,f24,f23])).

fof(f34,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_380,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_382,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_389,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1753,plain,
    ( k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_382,c_389])).

cnf(c_2156,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_380,c_1753])).

cnf(c_5,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_388,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2387,plain,
    ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) = iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2156,c_388])).

cnf(c_14,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5995,plain,
    ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2387,c_14,c_15])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_385,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_387,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_710,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_385,c_387])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1321,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_710,c_14,c_15,c_18])).

cnf(c_1322,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(renaming,[status(thm)],[c_1321])).

cnf(c_2385,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2156,c_1322])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_392,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2741,plain,
    ( k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2385,c_392])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_391,plain,
    ( k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k2_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_913,plain,
    ( k2_xboole_0(k9_relat_1(sK0,X0),k9_relat_1(sK0,X1)) = k9_relat_1(sK0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_380,c_391])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_393,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1021,plain,
    ( r1_tarski(k9_relat_1(sK0,X0),X1) = iProver_top
    | r1_tarski(k9_relat_1(sK0,k2_xboole_0(X0,X2)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_913,c_393])).

cnf(c_2840,plain,
    ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0) != iProver_top
    | r1_tarski(k9_relat_1(sK0,sK2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2741,c_1021])).

cnf(c_16176,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5995,c_2840])).

cnf(c_3,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_390,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2388,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2156,c_390])).

cnf(c_3669,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2388,c_14])).

cnf(c_2842,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2741,c_393])).

cnf(c_4250,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3669,c_2842])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_20,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16176,c_4250,c_2385,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.17/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.17/1.51  
% 7.17/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.17/1.51  
% 7.17/1.51  ------  iProver source info
% 7.17/1.51  
% 7.17/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.17/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.17/1.51  git: non_committed_changes: false
% 7.17/1.51  git: last_make_outside_of_git: false
% 7.17/1.51  
% 7.17/1.51  ------ 
% 7.17/1.51  ------ Parsing...
% 7.17/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.17/1.51  
% 7.17/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.17/1.51  
% 7.17/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.17/1.51  
% 7.17/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.17/1.51  ------ Proving...
% 7.17/1.51  ------ Problem Properties 
% 7.17/1.51  
% 7.17/1.51  
% 7.17/1.51  clauses                                 14
% 7.17/1.51  conjectures                             7
% 7.17/1.51  EPR                                     4
% 7.17/1.51  Horn                                    12
% 7.17/1.51  unary                                   4
% 7.17/1.51  binary                                  6
% 7.17/1.51  lits                                    30
% 7.17/1.51  lits eq                                 3
% 7.17/1.51  fd_pure                                 0
% 7.17/1.51  fd_pseudo                               0
% 7.17/1.51  fd_cond                                 0
% 7.17/1.51  fd_pseudo_cond                          0
% 7.17/1.51  AC symbols                              0
% 7.17/1.51  
% 7.17/1.51  ------ Input Options Time Limit: Unbounded
% 7.17/1.51  
% 7.17/1.51  
% 7.17/1.51  ------ 
% 7.17/1.51  Current options:
% 7.17/1.51  ------ 
% 7.17/1.51  
% 7.17/1.51  
% 7.17/1.51  
% 7.17/1.51  
% 7.17/1.51  ------ Proving...
% 7.17/1.51  
% 7.17/1.51  
% 7.17/1.51  % SZS status Theorem for theBenchmark.p
% 7.17/1.51  
% 7.17/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.17/1.51  
% 7.17/1.51  fof(f8,conjecture,(
% 7.17/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 7.17/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.17/1.51  
% 7.17/1.51  fof(f9,negated_conjecture,(
% 7.17/1.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 7.17/1.51    inference(negated_conjecture,[],[f8])).
% 7.17/1.51  
% 7.17/1.51  fof(f19,plain,(
% 7.17/1.51    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 7.17/1.51    inference(ennf_transformation,[],[f9])).
% 7.17/1.51  
% 7.17/1.51  fof(f20,plain,(
% 7.17/1.51    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.17/1.51    inference(flattening,[],[f19])).
% 7.17/1.51  
% 7.17/1.51  fof(f21,plain,(
% 7.17/1.51    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.17/1.51    inference(nnf_transformation,[],[f20])).
% 7.17/1.51  
% 7.17/1.51  fof(f22,plain,(
% 7.17/1.51    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.17/1.51    inference(flattening,[],[f21])).
% 7.17/1.51  
% 7.17/1.51  fof(f25,plain,(
% 7.17/1.51    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) => ((~r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1)) | ~r1_tarski(sK2,k1_relat_1(X0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1)) & r1_tarski(sK2,k1_relat_1(X0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1)))))) )),
% 7.17/1.51    introduced(choice_axiom,[])).
% 7.17/1.51  
% 7.17/1.51  fof(f24,plain,(
% 7.17/1.51    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1))) )),
% 7.17/1.51    introduced(choice_axiom,[])).
% 7.17/1.51  
% 7.17/1.51  fof(f23,plain,(
% 7.17/1.51    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 7.17/1.51    introduced(choice_axiom,[])).
% 7.17/1.51  
% 7.17/1.51  fof(f26,plain,(
% 7.17/1.51    (((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 7.17/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25,f24,f23])).
% 7.17/1.51  
% 7.17/1.51  fof(f34,plain,(
% 7.17/1.51    v1_relat_1(sK0)),
% 7.17/1.51    inference(cnf_transformation,[],[f26])).
% 7.17/1.51  
% 7.17/1.51  fof(f36,plain,(
% 7.17/1.51    v1_relat_1(sK1)),
% 7.17/1.51    inference(cnf_transformation,[],[f26])).
% 7.17/1.51  
% 7.17/1.51  fof(f5,axiom,(
% 7.17/1.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 7.17/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.17/1.51  
% 7.17/1.51  fof(f14,plain,(
% 7.17/1.51    ! [X0] : (! [X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.17/1.51    inference(ennf_transformation,[],[f5])).
% 7.17/1.51  
% 7.17/1.51  fof(f31,plain,(
% 7.17/1.51    ( ! [X0,X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.17/1.51    inference(cnf_transformation,[],[f14])).
% 7.17/1.51  
% 7.17/1.51  fof(f6,axiom,(
% 7.17/1.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 7.17/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.17/1.51  
% 7.17/1.51  fof(f15,plain,(
% 7.17/1.51    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.17/1.51    inference(ennf_transformation,[],[f6])).
% 7.17/1.51  
% 7.17/1.51  fof(f16,plain,(
% 7.17/1.51    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.17/1.51    inference(flattening,[],[f15])).
% 7.17/1.51  
% 7.17/1.51  fof(f32,plain,(
% 7.17/1.51    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.17/1.51    inference(cnf_transformation,[],[f16])).
% 7.17/1.51  
% 7.17/1.51  fof(f35,plain,(
% 7.17/1.51    v1_funct_1(sK0)),
% 7.17/1.51    inference(cnf_transformation,[],[f26])).
% 7.17/1.51  
% 7.17/1.51  fof(f39,plain,(
% 7.17/1.51    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 7.17/1.51    inference(cnf_transformation,[],[f26])).
% 7.17/1.51  
% 7.17/1.51  fof(f7,axiom,(
% 7.17/1.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 7.17/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.17/1.51  
% 7.17/1.51  fof(f17,plain,(
% 7.17/1.51    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.17/1.51    inference(ennf_transformation,[],[f7])).
% 7.17/1.51  
% 7.17/1.51  fof(f18,plain,(
% 7.17/1.51    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.17/1.51    inference(flattening,[],[f17])).
% 7.17/1.51  
% 7.17/1.51  fof(f33,plain,(
% 7.17/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.17/1.51    inference(cnf_transformation,[],[f18])).
% 7.17/1.51  
% 7.17/1.51  fof(f38,plain,(
% 7.17/1.51    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 7.17/1.51    inference(cnf_transformation,[],[f26])).
% 7.17/1.51  
% 7.17/1.51  fof(f2,axiom,(
% 7.17/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.17/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.17/1.51  
% 7.17/1.51  fof(f11,plain,(
% 7.17/1.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.17/1.51    inference(ennf_transformation,[],[f2])).
% 7.17/1.51  
% 7.17/1.51  fof(f28,plain,(
% 7.17/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.17/1.51    inference(cnf_transformation,[],[f11])).
% 7.17/1.51  
% 7.17/1.51  fof(f3,axiom,(
% 7.17/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)))),
% 7.17/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.17/1.51  
% 7.17/1.51  fof(f12,plain,(
% 7.17/1.51    ! [X0,X1,X2] : (k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.17/1.51    inference(ennf_transformation,[],[f3])).
% 7.17/1.51  
% 7.17/1.51  fof(f29,plain,(
% 7.17/1.51    ( ! [X2,X0,X1] : (k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 7.17/1.51    inference(cnf_transformation,[],[f12])).
% 7.17/1.51  
% 7.17/1.51  fof(f1,axiom,(
% 7.17/1.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 7.17/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.17/1.51  
% 7.17/1.51  fof(f10,plain,(
% 7.17/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 7.17/1.51    inference(ennf_transformation,[],[f1])).
% 7.17/1.51  
% 7.17/1.51  fof(f27,plain,(
% 7.17/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 7.17/1.51    inference(cnf_transformation,[],[f10])).
% 7.17/1.51  
% 7.17/1.51  fof(f4,axiom,(
% 7.17/1.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 7.17/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.17/1.51  
% 7.17/1.51  fof(f13,plain,(
% 7.17/1.51    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.17/1.51    inference(ennf_transformation,[],[f4])).
% 7.17/1.51  
% 7.17/1.51  fof(f30,plain,(
% 7.17/1.51    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.17/1.51    inference(cnf_transformation,[],[f13])).
% 7.17/1.51  
% 7.17/1.51  fof(f40,plain,(
% 7.17/1.51    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 7.17/1.51    inference(cnf_transformation,[],[f26])).
% 7.17/1.51  
% 7.17/1.51  cnf(c_13,negated_conjecture,
% 7.17/1.51      ( v1_relat_1(sK0) ),
% 7.17/1.51      inference(cnf_transformation,[],[f34]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_380,plain,
% 7.17/1.51      ( v1_relat_1(sK0) = iProver_top ),
% 7.17/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_11,negated_conjecture,
% 7.17/1.51      ( v1_relat_1(sK1) ),
% 7.17/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_382,plain,
% 7.17/1.51      ( v1_relat_1(sK1) = iProver_top ),
% 7.17/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_4,plain,
% 7.17/1.51      ( ~ v1_relat_1(X0)
% 7.17/1.51      | ~ v1_relat_1(X1)
% 7.17/1.51      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ),
% 7.17/1.51      inference(cnf_transformation,[],[f31]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_389,plain,
% 7.17/1.51      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
% 7.17/1.51      | v1_relat_1(X1) != iProver_top
% 7.17/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.17/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_1753,plain,
% 7.17/1.51      ( k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1))
% 7.17/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.17/1.51      inference(superposition,[status(thm)],[c_382,c_389]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_2156,plain,
% 7.17/1.51      ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
% 7.17/1.51      inference(superposition,[status(thm)],[c_380,c_1753]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_5,plain,
% 7.17/1.51      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 7.17/1.51      | ~ v1_funct_1(X0)
% 7.17/1.51      | ~ v1_relat_1(X0) ),
% 7.17/1.51      inference(cnf_transformation,[],[f32]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_388,plain,
% 7.17/1.51      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 7.17/1.51      | v1_funct_1(X0) != iProver_top
% 7.17/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.17/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_2387,plain,
% 7.17/1.51      ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) = iProver_top
% 7.17/1.51      | v1_funct_1(sK0) != iProver_top
% 7.17/1.51      | v1_relat_1(sK0) != iProver_top ),
% 7.17/1.51      inference(superposition,[status(thm)],[c_2156,c_388]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_14,plain,
% 7.17/1.51      ( v1_relat_1(sK0) = iProver_top ),
% 7.17/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_12,negated_conjecture,
% 7.17/1.51      ( v1_funct_1(sK0) ),
% 7.17/1.51      inference(cnf_transformation,[],[f35]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_15,plain,
% 7.17/1.51      ( v1_funct_1(sK0) = iProver_top ),
% 7.17/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_5995,plain,
% 7.17/1.51      ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) = iProver_top ),
% 7.17/1.51      inference(global_propositional_subsumption,
% 7.17/1.51                [status(thm)],
% 7.17/1.51                [c_2387,c_14,c_15]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_8,negated_conjecture,
% 7.17/1.51      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
% 7.17/1.51      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
% 7.17/1.51      inference(cnf_transformation,[],[f39]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_385,plain,
% 7.17/1.51      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top
% 7.17/1.51      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 7.17/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_6,plain,
% 7.17/1.51      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 7.17/1.51      | ~ r1_tarski(X0,k1_relat_1(X1))
% 7.17/1.51      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 7.17/1.51      | ~ v1_funct_1(X1)
% 7.17/1.51      | ~ v1_relat_1(X1) ),
% 7.17/1.51      inference(cnf_transformation,[],[f33]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_387,plain,
% 7.17/1.51      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 7.17/1.51      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 7.17/1.51      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 7.17/1.51      | v1_funct_1(X1) != iProver_top
% 7.17/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.17/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_710,plain,
% 7.17/1.51      ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
% 7.17/1.51      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 7.17/1.51      | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top
% 7.17/1.51      | v1_funct_1(sK0) != iProver_top
% 7.17/1.51      | v1_relat_1(sK0) != iProver_top ),
% 7.17/1.51      inference(superposition,[status(thm)],[c_385,c_387]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_9,negated_conjecture,
% 7.17/1.51      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 7.17/1.51      | r1_tarski(sK2,k1_relat_1(sK0)) ),
% 7.17/1.51      inference(cnf_transformation,[],[f38]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_18,plain,
% 7.17/1.51      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 7.17/1.51      | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
% 7.17/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_1321,plain,
% 7.17/1.51      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 7.17/1.51      | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top ),
% 7.17/1.51      inference(global_propositional_subsumption,
% 7.17/1.51                [status(thm)],
% 7.17/1.51                [c_710,c_14,c_15,c_18]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_1322,plain,
% 7.17/1.51      ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
% 7.17/1.51      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 7.17/1.51      inference(renaming,[status(thm)],[c_1321]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_2385,plain,
% 7.17/1.51      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 7.17/1.51      inference(demodulation,[status(thm)],[c_2156,c_1322]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_1,plain,
% 7.17/1.51      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.17/1.51      inference(cnf_transformation,[],[f28]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_392,plain,
% 7.17/1.51      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 7.17/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_2741,plain,
% 7.17/1.51      ( k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
% 7.17/1.51      inference(superposition,[status(thm)],[c_2385,c_392]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_2,plain,
% 7.17/1.51      ( ~ v1_relat_1(X0)
% 7.17/1.51      | k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 7.17/1.51      inference(cnf_transformation,[],[f29]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_391,plain,
% 7.17/1.51      ( k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k2_xboole_0(X1,X2))
% 7.17/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.17/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_913,plain,
% 7.17/1.51      ( k2_xboole_0(k9_relat_1(sK0,X0),k9_relat_1(sK0,X1)) = k9_relat_1(sK0,k2_xboole_0(X0,X1)) ),
% 7.17/1.51      inference(superposition,[status(thm)],[c_380,c_391]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_0,plain,
% 7.17/1.51      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 7.17/1.51      inference(cnf_transformation,[],[f27]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_393,plain,
% 7.17/1.51      ( r1_tarski(X0,X1) = iProver_top
% 7.17/1.51      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 7.17/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_1021,plain,
% 7.17/1.51      ( r1_tarski(k9_relat_1(sK0,X0),X1) = iProver_top
% 7.17/1.51      | r1_tarski(k9_relat_1(sK0,k2_xboole_0(X0,X2)),X1) != iProver_top ),
% 7.17/1.51      inference(superposition,[status(thm)],[c_913,c_393]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_2840,plain,
% 7.17/1.51      ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0) != iProver_top
% 7.17/1.51      | r1_tarski(k9_relat_1(sK0,sK2),X0) = iProver_top ),
% 7.17/1.51      inference(superposition,[status(thm)],[c_2741,c_1021]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_16176,plain,
% 7.17/1.51      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top ),
% 7.17/1.51      inference(superposition,[status(thm)],[c_5995,c_2840]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_3,plain,
% 7.17/1.51      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.17/1.51      inference(cnf_transformation,[],[f30]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_390,plain,
% 7.17/1.51      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.17/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.17/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_2388,plain,
% 7.17/1.51      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) = iProver_top
% 7.17/1.51      | v1_relat_1(sK0) != iProver_top ),
% 7.17/1.51      inference(superposition,[status(thm)],[c_2156,c_390]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_3669,plain,
% 7.17/1.51      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) = iProver_top ),
% 7.17/1.51      inference(global_propositional_subsumption,
% 7.17/1.51                [status(thm)],
% 7.17/1.51                [c_2388,c_14]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_2842,plain,
% 7.17/1.51      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0) != iProver_top
% 7.17/1.51      | r1_tarski(sK2,X0) = iProver_top ),
% 7.17/1.51      inference(superposition,[status(thm)],[c_2741,c_393]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_4250,plain,
% 7.17/1.51      ( r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
% 7.17/1.51      inference(superposition,[status(thm)],[c_3669,c_2842]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_7,negated_conjecture,
% 7.17/1.51      ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
% 7.17/1.51      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 7.17/1.51      | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
% 7.17/1.51      inference(cnf_transformation,[],[f40]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(c_20,plain,
% 7.17/1.51      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) != iProver_top
% 7.17/1.51      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) != iProver_top
% 7.17/1.51      | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top ),
% 7.17/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.17/1.51  
% 7.17/1.51  cnf(contradiction,plain,
% 7.17/1.51      ( $false ),
% 7.17/1.51      inference(minisat,[status(thm)],[c_16176,c_4250,c_2385,c_20]) ).
% 7.17/1.51  
% 7.17/1.51  
% 7.17/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.17/1.51  
% 7.17/1.51  ------                               Statistics
% 7.17/1.51  
% 7.17/1.51  ------ Selected
% 7.17/1.51  
% 7.17/1.51  total_time:                             0.827
% 7.17/1.51  
%------------------------------------------------------------------------------
