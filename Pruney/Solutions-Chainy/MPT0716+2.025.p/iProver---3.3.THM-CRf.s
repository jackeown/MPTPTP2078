%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:56 EST 2020

% Result     : Theorem 11.37s
% Output     : CNFRefutation 11.37s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 363 expanded)
%              Number of clauses        :   49 (  92 expanded)
%              Number of leaves         :   13 (  98 expanded)
%              Depth                    :   18
%              Number of atoms          :  301 (2563 expanded)
%              Number of equality atoms :   71 ( 124 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_371,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_373,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_381,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1753,plain,
    ( k10_relat_1(X0,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(X0,sK1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_373,c_381])).

cnf(c_2038,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_371,c_1753])).

cnf(c_5,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_379,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2179,plain,
    ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) = iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2038,c_379])).

cnf(c_14,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2883,plain,
    ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2179,c_14,c_15])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_376,plain,
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

cnf(c_378,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_724,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_376,c_378])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1271,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_724,c_14,c_15,c_18])).

cnf(c_1272,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(renaming,[status(thm)],[c_1271])).

cnf(c_2168,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2038,c_1272])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_382,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_383,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1771,plain,
    ( k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,X2)
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_382,c_383])).

cnf(c_10592,plain,
    ( k2_xboole_0(k9_relat_1(X0,sK2),k9_relat_1(X0,k1_relat_1(k5_relat_1(sK0,sK1)))) = k9_relat_1(X0,k1_relat_1(k5_relat_1(sK0,sK1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2168,c_1771])).

cnf(c_29520,plain,
    ( k2_xboole_0(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))) = k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_371,c_10592])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_384,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_30479,plain,
    ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0) != iProver_top
    | r1_tarski(k9_relat_1(sK0,sK2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_29520,c_384])).

cnf(c_30651,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2883,c_30479])).

cnf(c_129,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_127,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1303,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_129,c_127])).

cnf(c_1317,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(resolution,[status(thm)],[c_1303,c_1])).

cnf(c_1382,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(resolution,[status(thm)],[c_0,c_1317])).

cnf(c_1404,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0)
    | r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(resolution,[status(thm)],[c_1382,c_9])).

cnf(c_4,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1418,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[status(thm)],[c_1404,c_4])).

cnf(c_1419,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1418])).

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

cnf(c_16,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30651,c_2168,c_1419,c_20,c_16,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:22:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 11.37/2.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.37/2.01  
% 11.37/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.37/2.01  
% 11.37/2.01  ------  iProver source info
% 11.37/2.01  
% 11.37/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.37/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.37/2.01  git: non_committed_changes: false
% 11.37/2.01  git: last_make_outside_of_git: false
% 11.37/2.01  
% 11.37/2.01  ------ 
% 11.37/2.01  ------ Parsing...
% 11.37/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.37/2.01  
% 11.37/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.37/2.01  
% 11.37/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.37/2.01  
% 11.37/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.37/2.01  ------ Proving...
% 11.37/2.01  ------ Problem Properties 
% 11.37/2.01  
% 11.37/2.01  
% 11.37/2.01  clauses                                 14
% 11.37/2.01  conjectures                             7
% 11.37/2.01  EPR                                     4
% 11.37/2.01  Horn                                    12
% 11.37/2.01  unary                                   4
% 11.37/2.01  binary                                  4
% 11.37/2.01  lits                                    32
% 11.37/2.01  lits eq                                 2
% 11.37/2.01  fd_pure                                 0
% 11.37/2.01  fd_pseudo                               0
% 11.37/2.01  fd_cond                                 0
% 11.37/2.01  fd_pseudo_cond                          0
% 11.37/2.01  AC symbols                              0
% 11.37/2.01  
% 11.37/2.01  ------ Input Options Time Limit: Unbounded
% 11.37/2.01  
% 11.37/2.01  
% 11.37/2.01  ------ 
% 11.37/2.01  Current options:
% 11.37/2.01  ------ 
% 11.37/2.01  
% 11.37/2.01  
% 11.37/2.01  
% 11.37/2.01  
% 11.37/2.01  ------ Proving...
% 11.37/2.01  
% 11.37/2.01  
% 11.37/2.01  % SZS status Theorem for theBenchmark.p
% 11.37/2.01  
% 11.37/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.37/2.01  
% 11.37/2.01  fof(f8,conjecture,(
% 11.37/2.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 11.37/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.37/2.01  
% 11.37/2.01  fof(f9,negated_conjecture,(
% 11.37/2.01    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 11.37/2.01    inference(negated_conjecture,[],[f8])).
% 11.37/2.01  
% 11.37/2.01  fof(f20,plain,(
% 11.37/2.01    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 11.37/2.01    inference(ennf_transformation,[],[f9])).
% 11.37/2.01  
% 11.37/2.01  fof(f21,plain,(
% 11.37/2.01    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 11.37/2.01    inference(flattening,[],[f20])).
% 11.37/2.01  
% 11.37/2.01  fof(f22,plain,(
% 11.37/2.01    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 11.37/2.01    inference(nnf_transformation,[],[f21])).
% 11.37/2.01  
% 11.37/2.01  fof(f23,plain,(
% 11.37/2.01    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 11.37/2.01    inference(flattening,[],[f22])).
% 11.37/2.01  
% 11.37/2.01  fof(f26,plain,(
% 11.37/2.01    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) => ((~r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1)) | ~r1_tarski(sK2,k1_relat_1(X0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,sK2),k1_relat_1(X1)) & r1_tarski(sK2,k1_relat_1(X0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(X0,X1)))))) )),
% 11.37/2.01    introduced(choice_axiom,[])).
% 11.37/2.01  
% 11.37/2.01  fof(f25,plain,(
% 11.37/2.01    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1))) )),
% 11.37/2.01    introduced(choice_axiom,[])).
% 11.37/2.01  
% 11.37/2.01  fof(f24,plain,(
% 11.37/2.01    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 11.37/2.01    introduced(choice_axiom,[])).
% 11.37/2.01  
% 11.37/2.01  fof(f27,plain,(
% 11.37/2.01    (((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 11.37/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).
% 11.37/2.01  
% 11.37/2.01  fof(f35,plain,(
% 11.37/2.01    v1_relat_1(sK0)),
% 11.37/2.01    inference(cnf_transformation,[],[f27])).
% 11.37/2.01  
% 11.37/2.01  fof(f37,plain,(
% 11.37/2.01    v1_relat_1(sK1)),
% 11.37/2.01    inference(cnf_transformation,[],[f27])).
% 11.37/2.01  
% 11.37/2.01  fof(f4,axiom,(
% 11.37/2.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 11.37/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.37/2.01  
% 11.37/2.01  fof(f14,plain,(
% 11.37/2.01    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.37/2.01    inference(ennf_transformation,[],[f4])).
% 11.37/2.01  
% 11.37/2.01  fof(f31,plain,(
% 11.37/2.01    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.37/2.01    inference(cnf_transformation,[],[f14])).
% 11.37/2.01  
% 11.37/2.01  fof(f6,axiom,(
% 11.37/2.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 11.37/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.37/2.01  
% 11.37/2.01  fof(f16,plain,(
% 11.37/2.01    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.37/2.01    inference(ennf_transformation,[],[f6])).
% 11.37/2.01  
% 11.37/2.01  fof(f17,plain,(
% 11.37/2.01    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.37/2.01    inference(flattening,[],[f16])).
% 11.37/2.01  
% 11.37/2.01  fof(f33,plain,(
% 11.37/2.01    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.37/2.01    inference(cnf_transformation,[],[f17])).
% 11.37/2.01  
% 11.37/2.01  fof(f36,plain,(
% 11.37/2.01    v1_funct_1(sK0)),
% 11.37/2.01    inference(cnf_transformation,[],[f27])).
% 11.37/2.01  
% 11.37/2.01  fof(f40,plain,(
% 11.37/2.01    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 11.37/2.01    inference(cnf_transformation,[],[f27])).
% 11.37/2.01  
% 11.37/2.01  fof(f7,axiom,(
% 11.37/2.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 11.37/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.37/2.01  
% 11.37/2.01  fof(f18,plain,(
% 11.37/2.01    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 11.37/2.01    inference(ennf_transformation,[],[f7])).
% 11.37/2.01  
% 11.37/2.01  fof(f19,plain,(
% 11.37/2.01    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.37/2.01    inference(flattening,[],[f18])).
% 11.37/2.01  
% 11.37/2.01  fof(f34,plain,(
% 11.37/2.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.37/2.01    inference(cnf_transformation,[],[f19])).
% 11.37/2.01  
% 11.37/2.01  fof(f39,plain,(
% 11.37/2.01    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 11.37/2.01    inference(cnf_transformation,[],[f27])).
% 11.37/2.01  
% 11.37/2.01  fof(f3,axiom,(
% 11.37/2.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 11.37/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.37/2.01  
% 11.37/2.01  fof(f12,plain,(
% 11.37/2.01    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 11.37/2.01    inference(ennf_transformation,[],[f3])).
% 11.37/2.01  
% 11.37/2.01  fof(f13,plain,(
% 11.37/2.01    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 11.37/2.01    inference(flattening,[],[f12])).
% 11.37/2.01  
% 11.37/2.01  fof(f30,plain,(
% 11.37/2.01    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 11.37/2.01    inference(cnf_transformation,[],[f13])).
% 11.37/2.01  
% 11.37/2.01  fof(f2,axiom,(
% 11.37/2.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.37/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.37/2.01  
% 11.37/2.01  fof(f11,plain,(
% 11.37/2.01    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.37/2.01    inference(ennf_transformation,[],[f2])).
% 11.37/2.01  
% 11.37/2.01  fof(f29,plain,(
% 11.37/2.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.37/2.01    inference(cnf_transformation,[],[f11])).
% 11.37/2.01  
% 11.37/2.01  fof(f1,axiom,(
% 11.37/2.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 11.37/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.37/2.01  
% 11.37/2.01  fof(f10,plain,(
% 11.37/2.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 11.37/2.01    inference(ennf_transformation,[],[f1])).
% 11.37/2.01  
% 11.37/2.01  fof(f28,plain,(
% 11.37/2.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 11.37/2.01    inference(cnf_transformation,[],[f10])).
% 11.37/2.01  
% 11.37/2.01  fof(f5,axiom,(
% 11.37/2.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 11.37/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.37/2.01  
% 11.37/2.01  fof(f15,plain,(
% 11.37/2.01    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.37/2.01    inference(ennf_transformation,[],[f5])).
% 11.37/2.01  
% 11.37/2.01  fof(f32,plain,(
% 11.37/2.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.37/2.01    inference(cnf_transformation,[],[f15])).
% 11.37/2.01  
% 11.37/2.01  fof(f41,plain,(
% 11.37/2.01    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 11.37/2.01    inference(cnf_transformation,[],[f27])).
% 11.37/2.01  
% 11.37/2.01  cnf(c_13,negated_conjecture,
% 11.37/2.01      ( v1_relat_1(sK0) ),
% 11.37/2.01      inference(cnf_transformation,[],[f35]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_371,plain,
% 11.37/2.01      ( v1_relat_1(sK0) = iProver_top ),
% 11.37/2.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_11,negated_conjecture,
% 11.37/2.01      ( v1_relat_1(sK1) ),
% 11.37/2.01      inference(cnf_transformation,[],[f37]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_373,plain,
% 11.37/2.01      ( v1_relat_1(sK1) = iProver_top ),
% 11.37/2.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_3,plain,
% 11.37/2.01      ( ~ v1_relat_1(X0)
% 11.37/2.01      | ~ v1_relat_1(X1)
% 11.37/2.01      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 11.37/2.01      inference(cnf_transformation,[],[f31]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_381,plain,
% 11.37/2.01      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 11.37/2.01      | v1_relat_1(X0) != iProver_top
% 11.37/2.01      | v1_relat_1(X1) != iProver_top ),
% 11.37/2.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_1753,plain,
% 11.37/2.01      ( k10_relat_1(X0,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(X0,sK1))
% 11.37/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.37/2.01      inference(superposition,[status(thm)],[c_373,c_381]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_2038,plain,
% 11.37/2.01      ( k10_relat_1(sK0,k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK0,sK1)) ),
% 11.37/2.01      inference(superposition,[status(thm)],[c_371,c_1753]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_5,plain,
% 11.37/2.01      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 11.37/2.01      | ~ v1_funct_1(X0)
% 11.37/2.01      | ~ v1_relat_1(X0) ),
% 11.37/2.01      inference(cnf_transformation,[],[f33]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_379,plain,
% 11.37/2.01      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 11.37/2.01      | v1_funct_1(X0) != iProver_top
% 11.37/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.37/2.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_2179,plain,
% 11.37/2.01      ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) = iProver_top
% 11.37/2.01      | v1_funct_1(sK0) != iProver_top
% 11.37/2.01      | v1_relat_1(sK0) != iProver_top ),
% 11.37/2.01      inference(superposition,[status(thm)],[c_2038,c_379]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_14,plain,
% 11.37/2.01      ( v1_relat_1(sK0) = iProver_top ),
% 11.37/2.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_12,negated_conjecture,
% 11.37/2.01      ( v1_funct_1(sK0) ),
% 11.37/2.01      inference(cnf_transformation,[],[f36]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_15,plain,
% 11.37/2.01      ( v1_funct_1(sK0) = iProver_top ),
% 11.37/2.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_2883,plain,
% 11.37/2.01      ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) = iProver_top ),
% 11.37/2.01      inference(global_propositional_subsumption,
% 11.37/2.01                [status(thm)],
% 11.37/2.01                [c_2179,c_14,c_15]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_8,negated_conjecture,
% 11.37/2.01      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
% 11.37/2.01      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
% 11.37/2.01      inference(cnf_transformation,[],[f40]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_376,plain,
% 11.37/2.01      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top
% 11.37/2.01      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 11.37/2.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_6,plain,
% 11.37/2.01      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 11.37/2.01      | ~ r1_tarski(X0,k1_relat_1(X1))
% 11.37/2.01      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 11.37/2.01      | ~ v1_funct_1(X1)
% 11.37/2.01      | ~ v1_relat_1(X1) ),
% 11.37/2.01      inference(cnf_transformation,[],[f34]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_378,plain,
% 11.37/2.01      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 11.37/2.01      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 11.37/2.01      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 11.37/2.01      | v1_funct_1(X1) != iProver_top
% 11.37/2.01      | v1_relat_1(X1) != iProver_top ),
% 11.37/2.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_724,plain,
% 11.37/2.01      ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
% 11.37/2.01      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 11.37/2.01      | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top
% 11.37/2.01      | v1_funct_1(sK0) != iProver_top
% 11.37/2.01      | v1_relat_1(sK0) != iProver_top ),
% 11.37/2.01      inference(superposition,[status(thm)],[c_376,c_378]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_9,negated_conjecture,
% 11.37/2.01      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 11.37/2.01      | r1_tarski(sK2,k1_relat_1(sK0)) ),
% 11.37/2.01      inference(cnf_transformation,[],[f39]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_18,plain,
% 11.37/2.01      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 11.37/2.01      | r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top ),
% 11.37/2.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_1271,plain,
% 11.37/2.01      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top
% 11.37/2.01      | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top ),
% 11.37/2.01      inference(global_propositional_subsumption,
% 11.37/2.01                [status(thm)],
% 11.37/2.01                [c_724,c_14,c_15,c_18]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_1272,plain,
% 11.37/2.01      ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) = iProver_top
% 11.37/2.01      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 11.37/2.01      inference(renaming,[status(thm)],[c_1271]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_2168,plain,
% 11.37/2.01      ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) = iProver_top ),
% 11.37/2.01      inference(demodulation,[status(thm)],[c_2038,c_1272]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_2,plain,
% 11.37/2.01      ( ~ r1_tarski(X0,X1)
% 11.37/2.01      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 11.37/2.01      | ~ v1_relat_1(X2) ),
% 11.37/2.01      inference(cnf_transformation,[],[f30]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_382,plain,
% 11.37/2.01      ( r1_tarski(X0,X1) != iProver_top
% 11.37/2.01      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
% 11.37/2.01      | v1_relat_1(X2) != iProver_top ),
% 11.37/2.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_1,plain,
% 11.37/2.01      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.37/2.01      inference(cnf_transformation,[],[f29]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_383,plain,
% 11.37/2.01      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.37/2.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_1771,plain,
% 11.37/2.01      ( k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,X2)
% 11.37/2.01      | r1_tarski(X1,X2) != iProver_top
% 11.37/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.37/2.01      inference(superposition,[status(thm)],[c_382,c_383]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_10592,plain,
% 11.37/2.01      ( k2_xboole_0(k9_relat_1(X0,sK2),k9_relat_1(X0,k1_relat_1(k5_relat_1(sK0,sK1)))) = k9_relat_1(X0,k1_relat_1(k5_relat_1(sK0,sK1)))
% 11.37/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.37/2.01      inference(superposition,[status(thm)],[c_2168,c_1771]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_29520,plain,
% 11.37/2.01      ( k2_xboole_0(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))) = k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))) ),
% 11.37/2.01      inference(superposition,[status(thm)],[c_371,c_10592]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_0,plain,
% 11.37/2.01      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 11.37/2.01      inference(cnf_transformation,[],[f28]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_384,plain,
% 11.37/2.01      ( r1_tarski(X0,X1) = iProver_top
% 11.37/2.01      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 11.37/2.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_30479,plain,
% 11.37/2.01      ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0) != iProver_top
% 11.37/2.01      | r1_tarski(k9_relat_1(sK0,sK2),X0) = iProver_top ),
% 11.37/2.01      inference(superposition,[status(thm)],[c_29520,c_384]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_30651,plain,
% 11.37/2.01      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) = iProver_top ),
% 11.37/2.01      inference(superposition,[status(thm)],[c_2883,c_30479]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_129,plain,
% 11.37/2.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.37/2.01      theory(equality) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_127,plain,( X0 = X0 ),theory(equality) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_1303,plain,
% 11.37/2.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.37/2.01      inference(resolution,[status(thm)],[c_129,c_127]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_1317,plain,
% 11.37/2.01      ( ~ r1_tarski(X0,X1)
% 11.37/2.01      | ~ r1_tarski(X2,X0)
% 11.37/2.01      | r1_tarski(k2_xboole_0(X2,X0),X1) ),
% 11.37/2.01      inference(resolution,[status(thm)],[c_1303,c_1]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_1382,plain,
% 11.37/2.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 11.37/2.01      inference(resolution,[status(thm)],[c_0,c_1317]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_1404,plain,
% 11.37/2.01      ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0)
% 11.37/2.01      | r1_tarski(sK2,X0)
% 11.37/2.01      | r1_tarski(sK2,k1_relat_1(sK0)) ),
% 11.37/2.01      inference(resolution,[status(thm)],[c_1382,c_9]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_4,plain,
% 11.37/2.01      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 11.37/2.01      | ~ v1_relat_1(X1)
% 11.37/2.01      | ~ v1_relat_1(X0) ),
% 11.37/2.01      inference(cnf_transformation,[],[f32]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_1418,plain,
% 11.37/2.01      ( r1_tarski(sK2,k1_relat_1(sK0))
% 11.37/2.01      | ~ v1_relat_1(sK1)
% 11.37/2.01      | ~ v1_relat_1(sK0) ),
% 11.37/2.01      inference(resolution,[status(thm)],[c_1404,c_4]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_1419,plain,
% 11.37/2.01      ( r1_tarski(sK2,k1_relat_1(sK0)) = iProver_top
% 11.37/2.01      | v1_relat_1(sK1) != iProver_top
% 11.37/2.01      | v1_relat_1(sK0) != iProver_top ),
% 11.37/2.01      inference(predicate_to_equality,[status(thm)],[c_1418]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_7,negated_conjecture,
% 11.37/2.01      ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
% 11.37/2.01      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
% 11.37/2.01      | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
% 11.37/2.01      inference(cnf_transformation,[],[f41]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_20,plain,
% 11.37/2.01      ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) != iProver_top
% 11.37/2.01      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) != iProver_top
% 11.37/2.01      | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top ),
% 11.37/2.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(c_16,plain,
% 11.37/2.01      ( v1_relat_1(sK1) = iProver_top ),
% 11.37/2.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.37/2.01  
% 11.37/2.01  cnf(contradiction,plain,
% 11.37/2.01      ( $false ),
% 11.37/2.01      inference(minisat,
% 11.37/2.01                [status(thm)],
% 11.37/2.01                [c_30651,c_2168,c_1419,c_20,c_16,c_14]) ).
% 11.37/2.01  
% 11.37/2.01  
% 11.37/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.37/2.01  
% 11.37/2.01  ------                               Statistics
% 11.37/2.01  
% 11.37/2.01  ------ Selected
% 11.37/2.01  
% 11.37/2.01  total_time:                             1.018
% 11.37/2.01  
%------------------------------------------------------------------------------
