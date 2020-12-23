%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:55 EST 2020

% Result     : Theorem 11.47s
% Output     : CNFRefutation 11.47s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 466 expanded)
%              Number of clauses        :   46 ( 119 expanded)
%              Number of leaves         :   11 ( 123 expanded)
%              Depth                    :   18
%              Number of atoms          :  282 (3284 expanded)
%              Number of equality atoms :   72 ( 174 expanded)
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
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f21])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f26,plain,(
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

fof(f25,plain,(
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

fof(f24,plain,
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

fof(f27,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).

fof(f35,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

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

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

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

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_374,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_376,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_383,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1818,plain,
    ( k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_376,c_383])).

cnf(c_2177,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_374,c_1818])).

cnf(c_5,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_382,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2262,plain,
    ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) = iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2177,c_382])).

cnf(c_14,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6177,plain,
    ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2262,c_14,c_15])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_379,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_381,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_723,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_379,c_381])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1254,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_723,c_14,c_15,c_18])).

cnf(c_1255,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(renaming,[status(thm)],[c_1254])).

cnf(c_2251,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2177,c_1255])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_385,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_386,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1836,plain,
    ( k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,X2)
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_385,c_386])).

cnf(c_8175,plain,
    ( k2_xboole_0(k9_relat_1(X0,sK2),k9_relat_1(X0,k1_relat_1(k5_relat_1(sK0,sK1)))) = k9_relat_1(X0,k1_relat_1(k5_relat_1(sK0,sK1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2251,c_1836])).

cnf(c_30606,plain,
    ( k2_xboole_0(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))) = k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_374,c_8175])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_387,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_30765,plain,
    ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0) != iProver_top
    | r1_tarski(k9_relat_1(sK0,sK2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_30606,c_387])).

cnf(c_32287,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6177,c_30765])).

cnf(c_3,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_384,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2263,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2177,c_384])).

cnf(c_4212,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2263,c_14])).

cnf(c_2573,plain,
    ( k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2251,c_386])).

cnf(c_2990,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2573,c_387])).

cnf(c_4485,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4212,c_2990])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_20,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32287,c_4485,c_2251,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:48:32 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 11.47/1.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.47/1.97  
% 11.47/1.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.47/1.97  
% 11.47/1.97  ------  iProver source info
% 11.47/1.97  
% 11.47/1.97  git: date: 2020-06-30 10:37:57 +0100
% 11.47/1.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.47/1.97  git: non_committed_changes: false
% 11.47/1.97  git: last_make_outside_of_git: false
% 11.47/1.97  
% 11.47/1.97  ------ 
% 11.47/1.97  ------ Parsing...
% 11.47/1.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.47/1.97  
% 11.47/1.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.47/1.97  
% 11.47/1.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.47/1.97  
% 11.47/1.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.47/1.97  ------ Proving...
% 11.47/1.97  ------ Problem Properties 
% 11.47/1.97  
% 11.47/1.97  
% 11.47/1.97  clauses                                 14
% 11.47/1.97  conjectures                             7
% 11.47/1.97  EPR                                     4
% 11.47/1.97  Horn                                    12
% 11.47/1.97  unary                                   4
% 11.47/1.97  binary                                  5
% 11.47/1.97  lits                                    31
% 11.47/1.97  lits eq                                 2
% 11.47/1.97  fd_pure                                 0
% 11.47/1.97  fd_pseudo                               0
% 11.47/1.97  fd_cond                                 0
% 11.47/1.97  fd_pseudo_cond                          0
% 11.47/1.97  AC symbols                              0
% 11.47/1.97  
% 11.47/1.97  ------ Input Options Time Limit: Unbounded
% 11.47/1.97  
% 11.47/1.97  
% 11.47/1.97  ------ 
% 11.47/1.97  Current options:
% 11.47/1.97  ------ 
% 11.47/1.97  
% 11.47/1.97  
% 11.47/1.97  
% 11.47/1.97  
% 11.47/1.97  ------ Proving...
% 11.47/1.97  
% 11.47/1.97  
% 11.47/1.97  % SZS status Theorem for theBenchmark.p
% 11.47/1.97  
% 11.47/1.97  % SZS output start CNFRefutation for theBenchmark.p
% 11.47/1.97  
% 11.47/1.97  fof(f8,conjecture,(
% 11.47/1.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 11.47/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.97  
% 11.47/1.97  fof(f9,negated_conjecture,(
% 11.47/1.97    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 11.47/1.97    inference(negated_conjecture,[],[f8])).
% 11.47/1.97  
% 11.47/1.97  fof(f20,plain,(
% 11.47/1.97    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 11.47/1.97    inference(ennf_transformation,[],[f9])).
% 11.47/1.97  
% 11.47/1.97  fof(f21,plain,(
% 11.47/1.97    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 11.47/1.97    inference(flattening,[],[f20])).
% 11.47/1.97  
% 11.47/1.97  fof(f22,plain,(
% 11.47/1.97    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 11.47/1.97    inference(nnf_transformation,[],[f21])).
% 11.47/1.97  
% 11.47/1.97  fof(f23,plain,(
% 11.47/1.97    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 11.47/1.97    inference(flattening,[],[f22])).
% 11.47/1.97  
% 11.47/1.97  fof(f26,plain,(
% 11.47/1.97    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) => ((~r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1)) | ~r1_tarski(sK2,k1_relat_1(X0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1)) & r1_tarski(sK2,k1_relat_1(X0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1)))))) )),
% 11.47/1.97    introduced(choice_axiom,[])).
% 11.47/1.97  
% 11.47/1.97  fof(f25,plain,(
% 11.47/1.97    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1))) )),
% 11.47/1.97    introduced(choice_axiom,[])).
% 11.47/1.97  
% 11.47/1.97  fof(f24,plain,(
% 11.47/1.97    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 11.47/1.97    introduced(choice_axiom,[])).
% 11.47/1.97  
% 11.47/1.97  fof(f27,plain,(
% 11.47/1.97    (((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 11.47/1.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).
% 11.47/1.97  
% 11.47/1.97  fof(f35,plain,(
% 11.47/1.97    v1_relat_1(sK0)),
% 11.47/1.97    inference(cnf_transformation,[],[f27])).
% 11.47/1.97  
% 11.47/1.97  fof(f37,plain,(
% 11.47/1.97    v1_relat_1(sK1)),
% 11.47/1.97    inference(cnf_transformation,[],[f27])).
% 11.47/1.97  
% 11.47/1.97  fof(f5,axiom,(
% 11.47/1.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 11.47/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.97  
% 11.47/1.97  fof(f15,plain,(
% 11.47/1.97    ! [X0] : (! [X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.47/1.97    inference(ennf_transformation,[],[f5])).
% 11.47/1.97  
% 11.47/1.97  fof(f32,plain,(
% 11.47/1.97    ( ! [X0,X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.47/1.97    inference(cnf_transformation,[],[f15])).
% 11.47/1.97  
% 11.47/1.97  fof(f6,axiom,(
% 11.47/1.97    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 11.47/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.97  
% 11.47/1.97  fof(f16,plain,(
% 11.47/1.97    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.47/1.97    inference(ennf_transformation,[],[f6])).
% 11.47/1.97  
% 11.47/1.97  fof(f17,plain,(
% 11.47/1.97    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.47/1.97    inference(flattening,[],[f16])).
% 11.47/1.97  
% 11.47/1.97  fof(f33,plain,(
% 11.47/1.97    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.47/1.97    inference(cnf_transformation,[],[f17])).
% 11.47/1.97  
% 11.47/1.97  fof(f36,plain,(
% 11.47/1.97    v1_funct_1(sK0)),
% 11.47/1.97    inference(cnf_transformation,[],[f27])).
% 11.47/1.97  
% 11.47/1.97  fof(f40,plain,(
% 11.47/1.97    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 11.47/1.97    inference(cnf_transformation,[],[f27])).
% 11.47/1.97  
% 11.47/1.97  fof(f7,axiom,(
% 11.47/1.97    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 11.47/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.97  
% 11.47/1.97  fof(f18,plain,(
% 11.47/1.97    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 11.47/1.97    inference(ennf_transformation,[],[f7])).
% 11.47/1.97  
% 11.47/1.97  fof(f19,plain,(
% 11.47/1.97    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.47/1.97    inference(flattening,[],[f18])).
% 11.47/1.97  
% 11.47/1.97  fof(f34,plain,(
% 11.47/1.97    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.47/1.97    inference(cnf_transformation,[],[f19])).
% 11.47/1.97  
% 11.47/1.97  fof(f39,plain,(
% 11.47/1.97    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 11.47/1.97    inference(cnf_transformation,[],[f27])).
% 11.47/1.97  
% 11.47/1.97  fof(f3,axiom,(
% 11.47/1.97    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 11.47/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.97  
% 11.47/1.97  fof(f12,plain,(
% 11.47/1.97    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 11.47/1.97    inference(ennf_transformation,[],[f3])).
% 11.47/1.97  
% 11.47/1.97  fof(f13,plain,(
% 11.47/1.97    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 11.47/1.97    inference(flattening,[],[f12])).
% 11.47/1.97  
% 11.47/1.97  fof(f30,plain,(
% 11.47/1.97    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 11.47/1.97    inference(cnf_transformation,[],[f13])).
% 11.47/1.97  
% 11.47/1.97  fof(f2,axiom,(
% 11.47/1.97    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.47/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.97  
% 11.47/1.97  fof(f11,plain,(
% 11.47/1.97    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.47/1.97    inference(ennf_transformation,[],[f2])).
% 11.47/1.97  
% 11.47/1.97  fof(f29,plain,(
% 11.47/1.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.47/1.97    inference(cnf_transformation,[],[f11])).
% 11.47/1.97  
% 11.47/1.97  fof(f1,axiom,(
% 11.47/1.97    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 11.47/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.97  
% 11.47/1.97  fof(f10,plain,(
% 11.47/1.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 11.47/1.97    inference(ennf_transformation,[],[f1])).
% 11.47/1.97  
% 11.47/1.97  fof(f28,plain,(
% 11.47/1.97    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 11.47/1.97    inference(cnf_transformation,[],[f10])).
% 11.47/1.97  
% 11.47/1.97  fof(f4,axiom,(
% 11.47/1.97    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 11.47/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.97  
% 11.47/1.97  fof(f14,plain,(
% 11.47/1.97    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.47/1.97    inference(ennf_transformation,[],[f4])).
% 11.47/1.97  
% 11.47/1.97  fof(f31,plain,(
% 11.47/1.97    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.47/1.97    inference(cnf_transformation,[],[f14])).
% 11.47/1.97  
% 11.47/1.97  fof(f41,plain,(
% 11.47/1.97    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 11.47/1.97    inference(cnf_transformation,[],[f27])).
% 11.47/1.97  
% 11.47/1.97  cnf(c_13,negated_conjecture,
% 11.47/1.97      ( v1_relat_1(sK0) ),
% 11.47/1.97      inference(cnf_transformation,[],[f35]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_374,plain,
% 11.47/1.97      ( v1_relat_1(sK0) = iProver_top ),
% 11.47/1.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_11,negated_conjecture,
% 11.47/1.97      ( v1_relat_1(sK1) ),
% 11.47/1.97      inference(cnf_transformation,[],[f37]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_376,plain,
% 11.47/1.97      ( v1_relat_1(sK1) = iProver_top ),
% 11.47/1.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_4,plain,
% 11.47/1.97      ( ~ v1_relat_1(X0)
% 11.47/1.97      | ~ v1_relat_1(X1)
% 11.47/1.97      | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
% 11.47/1.97      inference(cnf_transformation,[],[f32]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_383,plain,
% 11.47/1.97      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
% 11.47/1.97      | v1_relat_1(X0) != iProver_top
% 11.47/1.97      | v1_relat_1(X1) != iProver_top ),
% 11.47/1.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_1818,plain,
% 11.47/1.97      ( k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1))
% 11.47/1.97      | v1_relat_1(X0) != iProver_top ),
% 11.47/1.97      inference(superposition,[status(thm)],[c_376,c_383]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_2177,plain,
% 11.47/1.97      ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
% 11.47/1.97      inference(superposition,[status(thm)],[c_374,c_1818]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_5,plain,
% 11.47/1.97      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 11.47/1.97      | ~ v1_funct_1(X0)
% 11.47/1.97      | ~ v1_relat_1(X0) ),
% 11.47/1.97      inference(cnf_transformation,[],[f33]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_382,plain,
% 11.47/1.97      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 11.47/1.97      | v1_funct_1(X0) != iProver_top
% 11.47/1.97      | v1_relat_1(X0) != iProver_top ),
% 11.47/1.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_2262,plain,
% 11.47/1.97      ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) = iProver_top
% 11.47/1.97      | v1_funct_1(sK0) != iProver_top
% 11.47/1.97      | v1_relat_1(sK0) != iProver_top ),
% 11.47/1.97      inference(superposition,[status(thm)],[c_2177,c_382]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_14,plain,
% 11.47/1.97      ( v1_relat_1(sK0) = iProver_top ),
% 11.47/1.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_12,negated_conjecture,
% 11.47/1.97      ( v1_funct_1(sK0) ),
% 11.47/1.97      inference(cnf_transformation,[],[f36]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_15,plain,
% 11.47/1.97      ( v1_funct_1(sK0) = iProver_top ),
% 11.47/1.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_6177,plain,
% 11.47/1.97      ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) = iProver_top ),
% 11.47/1.97      inference(global_propositional_subsumption,
% 11.47/1.97                [status(thm)],
% 11.47/1.97                [c_2262,c_14,c_15]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_8,negated_conjecture,
% 11.47/1.97      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
% 11.47/1.97      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
% 11.47/1.97      inference(cnf_transformation,[],[f40]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_379,plain,
% 11.47/1.97      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top
% 11.47/1.97      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 11.47/1.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_6,plain,
% 11.47/1.97      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 11.47/1.97      | ~ r1_tarski(X0,k1_relat_1(X1))
% 11.47/1.97      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 11.47/1.97      | ~ v1_funct_1(X1)
% 11.47/1.97      | ~ v1_relat_1(X1) ),
% 11.47/1.97      inference(cnf_transformation,[],[f34]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_381,plain,
% 11.47/1.97      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 11.47/1.97      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 11.47/1.97      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 11.47/1.97      | v1_funct_1(X1) != iProver_top
% 11.47/1.97      | v1_relat_1(X1) != iProver_top ),
% 11.47/1.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_723,plain,
% 11.47/1.97      ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
% 11.47/1.97      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 11.47/1.97      | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top
% 11.47/1.97      | v1_funct_1(sK0) != iProver_top
% 11.47/1.97      | v1_relat_1(sK0) != iProver_top ),
% 11.47/1.97      inference(superposition,[status(thm)],[c_379,c_381]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_9,negated_conjecture,
% 11.47/1.97      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 11.47/1.97      | r1_tarski(sK2,k1_relat_1(sK0)) ),
% 11.47/1.97      inference(cnf_transformation,[],[f39]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_18,plain,
% 11.47/1.97      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 11.47/1.97      | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
% 11.47/1.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_1254,plain,
% 11.47/1.97      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 11.47/1.97      | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top ),
% 11.47/1.97      inference(global_propositional_subsumption,
% 11.47/1.97                [status(thm)],
% 11.47/1.97                [c_723,c_14,c_15,c_18]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_1255,plain,
% 11.47/1.97      ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
% 11.47/1.97      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 11.47/1.97      inference(renaming,[status(thm)],[c_1254]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_2251,plain,
% 11.47/1.97      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 11.47/1.97      inference(demodulation,[status(thm)],[c_2177,c_1255]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_2,plain,
% 11.47/1.97      ( ~ r1_tarski(X0,X1)
% 11.47/1.97      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 11.47/1.97      | ~ v1_relat_1(X2) ),
% 11.47/1.97      inference(cnf_transformation,[],[f30]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_385,plain,
% 11.47/1.97      ( r1_tarski(X0,X1) != iProver_top
% 11.47/1.97      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
% 11.47/1.97      | v1_relat_1(X2) != iProver_top ),
% 11.47/1.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_1,plain,
% 11.47/1.97      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.47/1.97      inference(cnf_transformation,[],[f29]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_386,plain,
% 11.47/1.97      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.47/1.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_1836,plain,
% 11.47/1.97      ( k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,X2)
% 11.47/1.97      | r1_tarski(X1,X2) != iProver_top
% 11.47/1.97      | v1_relat_1(X0) != iProver_top ),
% 11.47/1.97      inference(superposition,[status(thm)],[c_385,c_386]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_8175,plain,
% 11.47/1.97      ( k2_xboole_0(k9_relat_1(X0,sK2),k9_relat_1(X0,k1_relat_1(k5_relat_1(sK0,sK1)))) = k9_relat_1(X0,k1_relat_1(k5_relat_1(sK0,sK1)))
% 11.47/1.97      | v1_relat_1(X0) != iProver_top ),
% 11.47/1.97      inference(superposition,[status(thm)],[c_2251,c_1836]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_30606,plain,
% 11.47/1.97      ( k2_xboole_0(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))) = k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))) ),
% 11.47/1.97      inference(superposition,[status(thm)],[c_374,c_8175]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_0,plain,
% 11.47/1.97      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 11.47/1.97      inference(cnf_transformation,[],[f28]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_387,plain,
% 11.47/1.97      ( r1_tarski(X0,X1) = iProver_top
% 11.47/1.97      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 11.47/1.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_30765,plain,
% 11.47/1.97      ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0) != iProver_top
% 11.47/1.97      | r1_tarski(k9_relat_1(sK0,sK2),X0) = iProver_top ),
% 11.47/1.97      inference(superposition,[status(thm)],[c_30606,c_387]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_32287,plain,
% 11.47/1.97      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top ),
% 11.47/1.97      inference(superposition,[status(thm)],[c_6177,c_30765]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_3,plain,
% 11.47/1.97      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 11.47/1.97      inference(cnf_transformation,[],[f31]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_384,plain,
% 11.47/1.97      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 11.47/1.97      | v1_relat_1(X0) != iProver_top ),
% 11.47/1.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_2263,plain,
% 11.47/1.97      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) = iProver_top
% 11.47/1.97      | v1_relat_1(sK0) != iProver_top ),
% 11.47/1.97      inference(superposition,[status(thm)],[c_2177,c_384]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_4212,plain,
% 11.47/1.97      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) = iProver_top ),
% 11.47/1.97      inference(global_propositional_subsumption,
% 11.47/1.97                [status(thm)],
% 11.47/1.97                [c_2263,c_14]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_2573,plain,
% 11.47/1.97      ( k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
% 11.47/1.97      inference(superposition,[status(thm)],[c_2251,c_386]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_2990,plain,
% 11.47/1.97      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0) != iProver_top
% 11.47/1.97      | r1_tarski(sK2,X0) = iProver_top ),
% 11.47/1.97      inference(superposition,[status(thm)],[c_2573,c_387]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_4485,plain,
% 11.47/1.97      ( r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
% 11.47/1.97      inference(superposition,[status(thm)],[c_4212,c_2990]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_7,negated_conjecture,
% 11.47/1.97      ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
% 11.47/1.97      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 11.47/1.97      | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
% 11.47/1.97      inference(cnf_transformation,[],[f41]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(c_20,plain,
% 11.47/1.97      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) != iProver_top
% 11.47/1.97      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) != iProver_top
% 11.47/1.97      | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top ),
% 11.47/1.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.47/1.97  
% 11.47/1.97  cnf(contradiction,plain,
% 11.47/1.97      ( $false ),
% 11.47/1.97      inference(minisat,[status(thm)],[c_32287,c_4485,c_2251,c_20]) ).
% 11.47/1.97  
% 11.47/1.97  
% 11.47/1.97  % SZS output end CNFRefutation for theBenchmark.p
% 11.47/1.97  
% 11.47/1.97  ------                               Statistics
% 11.47/1.97  
% 11.47/1.97  ------ Selected
% 11.47/1.97  
% 11.47/1.97  total_time:                             1.275
% 11.47/1.97  
%------------------------------------------------------------------------------
