%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:55 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 577 expanded)
%              Number of clauses        :   60 ( 153 expanded)
%              Number of leaves         :   13 ( 159 expanded)
%              Depth                    :   20
%              Number of atoms          :  319 (4051 expanded)
%              Number of equality atoms :   86 ( 218 expanded)
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

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

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

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_377,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_379,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_387,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1735,plain,
    ( k10_relat_1(X0,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(X0,sK1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_379,c_387])).

cnf(c_1923,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_377,c_1735])).

cnf(c_5,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_385,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2102,plain,
    ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) = iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1923,c_385])).

cnf(c_14,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11505,plain,
    ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2102,c_14,c_15])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_382,plain,
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

cnf(c_384,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_730,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_382,c_384])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_129,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_759,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_131,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_539,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | X1 != k1_relat_1(k5_relat_1(sK0,sK1))
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_758,plain,
    ( r1_tarski(sK2,X0)
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | X0 != k1_relat_1(k5_relat_1(sK0,sK1))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_1238,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_1240,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1))
    | sK2 != sK2
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1238])).

cnf(c_1239,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | k10_relat_1(sK0,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1299,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_730,c_13,c_14,c_15,c_11,c_18,c_759,c_1240,c_1239])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_389,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1304,plain,
    ( k2_xboole_0(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_1299,c_389])).

cnf(c_2088,plain,
    ( k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_1923,c_1304])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_388,plain,
    ( k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k2_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_949,plain,
    ( k2_xboole_0(k9_relat_1(sK0,X0),k9_relat_1(sK0,X1)) = k9_relat_1(sK0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_377,c_388])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_390,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1066,plain,
    ( r1_tarski(k9_relat_1(sK0,X0),X1) = iProver_top
    | r1_tarski(k9_relat_1(sK0,k2_xboole_0(X0,X2)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_949,c_390])).

cnf(c_2495,plain,
    ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0) != iProver_top
    | r1_tarski(k9_relat_1(sK0,sK2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2088,c_1066])).

cnf(c_17743,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11505,c_2495])).

cnf(c_1572,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_131,c_129])).

cnf(c_1588,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(resolution,[status(thm)],[c_1572,c_1])).

cnf(c_1754,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(resolution,[status(thm)],[c_0,c_1588])).

cnf(c_1774,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0)
    | r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(resolution,[status(thm)],[c_1754,c_9])).

cnf(c_1306,plain,
    ( r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1304,c_390])).

cnf(c_2087,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1923,c_1306])).

cnf(c_2098,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0)
    | r1_tarski(sK2,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2087])).

cnf(c_2131,plain,
    ( r1_tarski(sK2,X0)
    | ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1774,c_2098])).

cnf(c_2132,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0)
    | r1_tarski(sK2,X0) ),
    inference(renaming,[status(thm)],[c_2131])).

cnf(c_4,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2147,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[status(thm)],[c_2132,c_4])).

cnf(c_2148,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2147])).

cnf(c_2089,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1923,c_1299])).

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

cnf(c_16,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17743,c_2148,c_2089,c_20,c_16,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:42:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.61/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.61/1.49  
% 7.61/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.61/1.49  
% 7.61/1.49  ------  iProver source info
% 7.61/1.49  
% 7.61/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.61/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.61/1.49  git: non_committed_changes: false
% 7.61/1.49  git: last_make_outside_of_git: false
% 7.61/1.49  
% 7.61/1.49  ------ 
% 7.61/1.49  ------ Parsing...
% 7.61/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.49  ------ Proving...
% 7.61/1.49  ------ Problem Properties 
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  clauses                                 14
% 7.61/1.49  conjectures                             7
% 7.61/1.49  EPR                                     4
% 7.61/1.49  Horn                                    12
% 7.61/1.49  unary                                   4
% 7.61/1.49  binary                                  5
% 7.61/1.49  lits                                    31
% 7.61/1.49  lits eq                                 3
% 7.61/1.49  fd_pure                                 0
% 7.61/1.49  fd_pseudo                               0
% 7.61/1.49  fd_cond                                 0
% 7.61/1.49  fd_pseudo_cond                          0
% 7.61/1.49  AC symbols                              0
% 7.61/1.49  
% 7.61/1.49  ------ Input Options Time Limit: Unbounded
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  ------ 
% 7.61/1.49  Current options:
% 7.61/1.49  ------ 
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  ------ Proving...
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  % SZS status Theorem for theBenchmark.p
% 7.61/1.49  
% 7.61/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.61/1.49  
% 7.61/1.49  fof(f8,conjecture,(
% 7.61/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f9,negated_conjecture,(
% 7.61/1.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 7.61/1.49    inference(negated_conjecture,[],[f8])).
% 7.61/1.49  
% 7.61/1.49  fof(f19,plain,(
% 7.61/1.49    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 7.61/1.49    inference(ennf_transformation,[],[f9])).
% 7.61/1.49  
% 7.61/1.49  fof(f20,plain,(
% 7.61/1.49    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.61/1.49    inference(flattening,[],[f19])).
% 7.61/1.49  
% 7.61/1.49  fof(f21,plain,(
% 7.61/1.49    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.61/1.49    inference(nnf_transformation,[],[f20])).
% 7.61/1.49  
% 7.61/1.49  fof(f22,plain,(
% 7.61/1.49    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.61/1.49    inference(flattening,[],[f21])).
% 7.61/1.49  
% 7.61/1.49  fof(f25,plain,(
% 7.61/1.49    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) => ((~r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1)) | ~r1_tarski(sK2,k1_relat_1(X0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1)) & r1_tarski(sK2,k1_relat_1(X0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1)))))) )),
% 7.61/1.49    introduced(choice_axiom,[])).
% 7.61/1.49  
% 7.61/1.49  fof(f24,plain,(
% 7.61/1.49    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1))) )),
% 7.61/1.49    introduced(choice_axiom,[])).
% 7.61/1.49  
% 7.61/1.49  fof(f23,plain,(
% 7.61/1.49    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 7.61/1.49    introduced(choice_axiom,[])).
% 7.61/1.49  
% 7.61/1.49  fof(f26,plain,(
% 7.61/1.49    (((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 7.61/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25,f24,f23])).
% 7.61/1.49  
% 7.61/1.49  fof(f34,plain,(
% 7.61/1.49    v1_relat_1(sK0)),
% 7.61/1.49    inference(cnf_transformation,[],[f26])).
% 7.61/1.49  
% 7.61/1.49  fof(f36,plain,(
% 7.61/1.49    v1_relat_1(sK1)),
% 7.61/1.49    inference(cnf_transformation,[],[f26])).
% 7.61/1.49  
% 7.61/1.49  fof(f4,axiom,(
% 7.61/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f13,plain,(
% 7.61/1.49    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.61/1.49    inference(ennf_transformation,[],[f4])).
% 7.61/1.49  
% 7.61/1.49  fof(f30,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f13])).
% 7.61/1.49  
% 7.61/1.49  fof(f6,axiom,(
% 7.61/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f15,plain,(
% 7.61/1.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.61/1.49    inference(ennf_transformation,[],[f6])).
% 7.61/1.49  
% 7.61/1.49  fof(f16,plain,(
% 7.61/1.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.61/1.49    inference(flattening,[],[f15])).
% 7.61/1.49  
% 7.61/1.49  fof(f32,plain,(
% 7.61/1.49    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f16])).
% 7.61/1.49  
% 7.61/1.49  fof(f35,plain,(
% 7.61/1.49    v1_funct_1(sK0)),
% 7.61/1.49    inference(cnf_transformation,[],[f26])).
% 7.61/1.49  
% 7.61/1.49  fof(f39,plain,(
% 7.61/1.49    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 7.61/1.49    inference(cnf_transformation,[],[f26])).
% 7.61/1.49  
% 7.61/1.49  fof(f7,axiom,(
% 7.61/1.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f17,plain,(
% 7.61/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.61/1.49    inference(ennf_transformation,[],[f7])).
% 7.61/1.49  
% 7.61/1.49  fof(f18,plain,(
% 7.61/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.61/1.49    inference(flattening,[],[f17])).
% 7.61/1.49  
% 7.61/1.49  fof(f33,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f18])).
% 7.61/1.49  
% 7.61/1.49  fof(f38,plain,(
% 7.61/1.49    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 7.61/1.49    inference(cnf_transformation,[],[f26])).
% 7.61/1.49  
% 7.61/1.49  fof(f2,axiom,(
% 7.61/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f11,plain,(
% 7.61/1.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.61/1.49    inference(ennf_transformation,[],[f2])).
% 7.61/1.49  
% 7.61/1.49  fof(f28,plain,(
% 7.61/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f11])).
% 7.61/1.49  
% 7.61/1.49  fof(f3,axiom,(
% 7.61/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f12,plain,(
% 7.61/1.49    ! [X0,X1,X2] : (k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.61/1.49    inference(ennf_transformation,[],[f3])).
% 7.61/1.49  
% 7.61/1.49  fof(f29,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f12])).
% 7.61/1.49  
% 7.61/1.49  fof(f1,axiom,(
% 7.61/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f10,plain,(
% 7.61/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 7.61/1.49    inference(ennf_transformation,[],[f1])).
% 7.61/1.49  
% 7.61/1.49  fof(f27,plain,(
% 7.61/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f10])).
% 7.61/1.49  
% 7.61/1.49  fof(f5,axiom,(
% 7.61/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 7.61/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.49  
% 7.61/1.49  fof(f14,plain,(
% 7.61/1.49    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.61/1.49    inference(ennf_transformation,[],[f5])).
% 7.61/1.49  
% 7.61/1.49  fof(f31,plain,(
% 7.61/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.61/1.49    inference(cnf_transformation,[],[f14])).
% 7.61/1.49  
% 7.61/1.49  fof(f40,plain,(
% 7.61/1.49    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 7.61/1.49    inference(cnf_transformation,[],[f26])).
% 7.61/1.49  
% 7.61/1.49  cnf(c_13,negated_conjecture,
% 7.61/1.49      ( v1_relat_1(sK0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_377,plain,
% 7.61/1.49      ( v1_relat_1(sK0) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_11,negated_conjecture,
% 7.61/1.49      ( v1_relat_1(sK1) ),
% 7.61/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_379,plain,
% 7.61/1.49      ( v1_relat_1(sK1) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_3,plain,
% 7.61/1.49      ( ~ v1_relat_1(X0)
% 7.61/1.49      | ~ v1_relat_1(X1)
% 7.61/1.49      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 7.61/1.49      inference(cnf_transformation,[],[f30]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_387,plain,
% 7.61/1.49      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 7.61/1.49      | v1_relat_1(X1) != iProver_top
% 7.61/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1735,plain,
% 7.61/1.49      ( k10_relat_1(X0,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(X0,sK1))
% 7.61/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_379,c_387]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1923,plain,
% 7.61/1.49      ( k10_relat_1(sK0,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_377,c_1735]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_5,plain,
% 7.61/1.49      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 7.61/1.49      | ~ v1_funct_1(X0)
% 7.61/1.49      | ~ v1_relat_1(X0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_385,plain,
% 7.61/1.49      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 7.61/1.49      | v1_funct_1(X0) != iProver_top
% 7.61/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_2102,plain,
% 7.61/1.49      ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) = iProver_top
% 7.61/1.49      | v1_funct_1(sK0) != iProver_top
% 7.61/1.49      | v1_relat_1(sK0) != iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_1923,c_385]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_14,plain,
% 7.61/1.49      ( v1_relat_1(sK0) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_12,negated_conjecture,
% 7.61/1.49      ( v1_funct_1(sK0) ),
% 7.61/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_15,plain,
% 7.61/1.49      ( v1_funct_1(sK0) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_11505,plain,
% 7.61/1.49      ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) = iProver_top ),
% 7.61/1.49      inference(global_propositional_subsumption,
% 7.61/1.49                [status(thm)],
% 7.61/1.49                [c_2102,c_14,c_15]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_8,negated_conjecture,
% 7.61/1.49      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
% 7.61/1.49      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
% 7.61/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_382,plain,
% 7.61/1.49      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top
% 7.61/1.49      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_6,plain,
% 7.61/1.49      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 7.61/1.49      | ~ r1_tarski(X0,k1_relat_1(X1))
% 7.61/1.49      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 7.61/1.49      | ~ v1_funct_1(X1)
% 7.61/1.49      | ~ v1_relat_1(X1) ),
% 7.61/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_384,plain,
% 7.61/1.49      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 7.61/1.49      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 7.61/1.49      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 7.61/1.49      | v1_funct_1(X1) != iProver_top
% 7.61/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_730,plain,
% 7.61/1.49      ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
% 7.61/1.49      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 7.61/1.49      | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top
% 7.61/1.49      | v1_funct_1(sK0) != iProver_top
% 7.61/1.49      | v1_relat_1(sK0) != iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_382,c_384]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_9,negated_conjecture,
% 7.61/1.49      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 7.61/1.49      | r1_tarski(sK2,k1_relat_1(sK0)) ),
% 7.61/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_18,plain,
% 7.61/1.49      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 7.61/1.49      | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_129,plain,( X0 = X0 ),theory(equality) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_759,plain,
% 7.61/1.49      ( sK2 = sK2 ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_129]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_131,plain,
% 7.61/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.61/1.49      theory(equality) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_539,plain,
% 7.61/1.49      ( r1_tarski(X0,X1)
% 7.61/1.49      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 7.61/1.49      | X1 != k1_relat_1(k5_relat_1(sK0,sK1))
% 7.61/1.49      | X0 != sK2 ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_131]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_758,plain,
% 7.61/1.49      ( r1_tarski(sK2,X0)
% 7.61/1.49      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 7.61/1.49      | X0 != k1_relat_1(k5_relat_1(sK0,sK1))
% 7.61/1.49      | sK2 != sK2 ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_539]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1238,plain,
% 7.61/1.49      ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
% 7.61/1.49      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 7.61/1.49      | k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1))
% 7.61/1.49      | sK2 != sK2 ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_758]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1240,plain,
% 7.61/1.49      ( k10_relat_1(sK0,k1_relat_1(sK1)) != k1_relat_1(k5_relat_1(sK0,sK1))
% 7.61/1.49      | sK2 != sK2
% 7.61/1.49      | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
% 7.61/1.49      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_1238]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1239,plain,
% 7.61/1.49      ( ~ v1_relat_1(sK1)
% 7.61/1.49      | ~ v1_relat_1(sK0)
% 7.61/1.49      | k10_relat_1(sK0,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1299,plain,
% 7.61/1.49      ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top ),
% 7.61/1.49      inference(global_propositional_subsumption,
% 7.61/1.49                [status(thm)],
% 7.61/1.49                [c_730,c_13,c_14,c_15,c_11,c_18,c_759,c_1240,c_1239]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1,plain,
% 7.61/1.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.61/1.49      inference(cnf_transformation,[],[f28]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_389,plain,
% 7.61/1.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1304,plain,
% 7.61/1.49      ( k2_xboole_0(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_1299,c_389]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_2088,plain,
% 7.61/1.49      ( k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
% 7.61/1.49      inference(demodulation,[status(thm)],[c_1923,c_1304]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_2,plain,
% 7.61/1.49      ( ~ v1_relat_1(X0)
% 7.61/1.49      | k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 7.61/1.49      inference(cnf_transformation,[],[f29]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_388,plain,
% 7.61/1.49      ( k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k2_xboole_0(X1,X2))
% 7.61/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_949,plain,
% 7.61/1.49      ( k2_xboole_0(k9_relat_1(sK0,X0),k9_relat_1(sK0,X1)) = k9_relat_1(sK0,k2_xboole_0(X0,X1)) ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_377,c_388]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_0,plain,
% 7.61/1.49      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 7.61/1.49      inference(cnf_transformation,[],[f27]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_390,plain,
% 7.61/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.61/1.49      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1066,plain,
% 7.61/1.49      ( r1_tarski(k9_relat_1(sK0,X0),X1) = iProver_top
% 7.61/1.49      | r1_tarski(k9_relat_1(sK0,k2_xboole_0(X0,X2)),X1) != iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_949,c_390]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_2495,plain,
% 7.61/1.49      ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0) != iProver_top
% 7.61/1.49      | r1_tarski(k9_relat_1(sK0,sK2),X0) = iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_2088,c_1066]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_17743,plain,
% 7.61/1.49      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_11505,c_2495]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1572,plain,
% 7.61/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.61/1.49      inference(resolution,[status(thm)],[c_131,c_129]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1588,plain,
% 7.61/1.49      ( ~ r1_tarski(X0,X1)
% 7.61/1.49      | ~ r1_tarski(X2,X0)
% 7.61/1.49      | r1_tarski(k2_xboole_0(X2,X0),X1) ),
% 7.61/1.49      inference(resolution,[status(thm)],[c_1572,c_1]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1754,plain,
% 7.61/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 7.61/1.49      inference(resolution,[status(thm)],[c_0,c_1588]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1774,plain,
% 7.61/1.49      ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0)
% 7.61/1.49      | r1_tarski(sK2,X0)
% 7.61/1.49      | r1_tarski(sK2,k1_relat_1(sK0)) ),
% 7.61/1.49      inference(resolution,[status(thm)],[c_1754,c_9]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1306,plain,
% 7.61/1.49      ( r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),X0) != iProver_top
% 7.61/1.49      | r1_tarski(sK2,X0) = iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_1304,c_390]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_2087,plain,
% 7.61/1.49      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0) != iProver_top
% 7.61/1.49      | r1_tarski(sK2,X0) = iProver_top ),
% 7.61/1.49      inference(demodulation,[status(thm)],[c_1923,c_1306]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_2098,plain,
% 7.61/1.49      ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0)
% 7.61/1.49      | r1_tarski(sK2,X0) ),
% 7.61/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_2087]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_2131,plain,
% 7.61/1.49      ( r1_tarski(sK2,X0)
% 7.61/1.49      | ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0) ),
% 7.61/1.49      inference(global_propositional_subsumption,
% 7.61/1.49                [status(thm)],
% 7.61/1.49                [c_1774,c_2098]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_2132,plain,
% 7.61/1.49      ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0)
% 7.61/1.49      | r1_tarski(sK2,X0) ),
% 7.61/1.49      inference(renaming,[status(thm)],[c_2131]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_4,plain,
% 7.61/1.49      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 7.61/1.49      | ~ v1_relat_1(X0)
% 7.61/1.49      | ~ v1_relat_1(X1) ),
% 7.61/1.49      inference(cnf_transformation,[],[f31]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_2147,plain,
% 7.61/1.49      ( r1_tarski(sK2,k1_relat_1(sK0))
% 7.61/1.49      | ~ v1_relat_1(sK1)
% 7.61/1.49      | ~ v1_relat_1(sK0) ),
% 7.61/1.49      inference(resolution,[status(thm)],[c_2132,c_4]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_2148,plain,
% 7.61/1.49      ( r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top
% 7.61/1.49      | v1_relat_1(sK1) != iProver_top
% 7.61/1.49      | v1_relat_1(sK0) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_2147]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_2089,plain,
% 7.61/1.49      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 7.61/1.49      inference(demodulation,[status(thm)],[c_1923,c_1299]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_7,negated_conjecture,
% 7.61/1.49      ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
% 7.61/1.49      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 7.61/1.49      | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
% 7.61/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_20,plain,
% 7.61/1.49      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) != iProver_top
% 7.61/1.49      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) != iProver_top
% 7.61/1.49      | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_16,plain,
% 7.61/1.49      ( v1_relat_1(sK1) = iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(contradiction,plain,
% 7.61/1.49      ( $false ),
% 7.61/1.49      inference(minisat,
% 7.61/1.49                [status(thm)],
% 7.61/1.49                [c_17743,c_2148,c_2089,c_20,c_16,c_14]) ).
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.61/1.49  
% 7.61/1.49  ------                               Statistics
% 7.61/1.49  
% 7.61/1.49  ------ Selected
% 7.61/1.49  
% 7.61/1.49  total_time:                             0.564
% 7.61/1.49  
%------------------------------------------------------------------------------
