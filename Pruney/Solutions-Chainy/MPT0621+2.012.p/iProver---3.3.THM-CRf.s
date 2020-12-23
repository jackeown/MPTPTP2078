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
% DateTime   : Thu Dec  3 11:49:22 EST 2020

% Result     : Theorem 7.54s
% Output     : CNFRefutation 7.54s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 460 expanded)
%              Number of clauses        :   71 ( 151 expanded)
%              Number of leaves         :   14 ( 112 expanded)
%              Depth                    :   25
%              Number of atoms          :  431 (2221 expanded)
%              Number of equality atoms :  290 (1180 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f25])).

fof(f45,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK2(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK2(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK2(X0,X1)) = X0
      & v1_funct_1(sK2(X0,X1))
      & v1_relat_1(sK2(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f23])).

fof(f41,plain,(
    ! [X0,X1] : k1_relat_1(sK2(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f8,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f13])).

fof(f27,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK4
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK4
              | k1_relat_1(X1) != sK4
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( k1_xboole_0 != sK4
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK4
            | k1_relat_1(X1) != sK4
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f27])).

fof(f47,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | k1_relat_1(X2) != sK4
      | k1_relat_1(X1) != sK4
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X0,X1] : v1_funct_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f38,f36])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK2(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f55,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f51])).

fof(f56,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f55])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f57,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f48,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_19659,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14,plain,
    ( k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( k1_relat_1(sK2(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,negated_conjecture,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_relat_1(X0) != sK4
    | k1_relat_1(X1) != sK4 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_19649,plain,
    ( X0 = X1
    | k1_relat_1(X0) != sK4
    | k1_relat_1(X1) != sK4
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20259,plain,
    ( sK2(X0,X1) = X2
    | k1_relat_1(X2) != sK4
    | sK4 != X0
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK2(X0,X1)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_19649])).

cnf(c_1284,plain,
    ( X0 = X1
    | k1_relat_1(X0) != sK4
    | k1_relat_1(X1) != sK4
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1701,plain,
    ( sK2(X0,X1) = X2
    | k1_relat_1(X2) != sK4
    | sK4 != X0
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK2(X0,X1)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_1284])).

cnf(c_12,plain,
    ( v1_relat_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_32,plain,
    ( v1_relat_1(sK2(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( v1_funct_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_35,plain,
    ( v1_funct_1(sK2(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1863,plain,
    ( v1_funct_1(X2) != iProver_top
    | sK2(X0,X1) = X2
    | k1_relat_1(X2) != sK4
    | sK4 != X0
    | v1_relat_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1701,c_32,c_35])).

cnf(c_1864,plain,
    ( sK2(X0,X1) = X2
    | k1_relat_1(X2) != sK4
    | sK4 != X0
    | v1_relat_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1863])).

cnf(c_20722,plain,
    ( v1_funct_1(X2) != iProver_top
    | sK2(X0,X1) = X2
    | k1_relat_1(X2) != sK4
    | sK4 != X0
    | v1_relat_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20259,c_32,c_35,c_1701])).

cnf(c_20723,plain,
    ( sK2(X0,X1) = X2
    | k1_relat_1(X2) != sK4
    | sK4 != X0
    | v1_relat_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_20722])).

cnf(c_20732,plain,
    ( sK2(X0,X1) = sK3(X2)
    | sK4 != X2
    | sK4 != X0
    | v1_relat_1(sK3(X2)) != iProver_top
    | v1_funct_1(sK3(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_20723])).

cnf(c_1426,plain,
    ( sK3(X0) = X1
    | k1_relat_1(X1) != sK4
    | sK4 != X0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK3(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1284])).

cnf(c_16,plain,
    ( v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_22,plain,
    ( v1_relat_1(sK3(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_25,plain,
    ( v1_funct_1(sK3(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1431,plain,
    ( v1_funct_1(X1) != iProver_top
    | sK3(X0) = X1
    | k1_relat_1(X1) != sK4
    | sK4 != X0
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1426,c_22,c_25])).

cnf(c_1432,plain,
    ( sK3(X0) = X1
    | k1_relat_1(X1) != sK4
    | sK4 != X0
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1431])).

cnf(c_1700,plain,
    ( sK2(X0,X1) = sK3(X2)
    | sK4 != X0
    | sK4 != X2
    | v1_relat_1(sK2(X0,X1)) != iProver_top
    | v1_funct_1(sK2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_1432])).

cnf(c_1726,plain,
    ( ~ v1_relat_1(sK2(X0,X1))
    | ~ v1_funct_1(sK2(X0,X1))
    | sK2(X0,X1) = sK3(X2)
    | sK4 != X0
    | sK4 != X2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1700])).

cnf(c_20756,plain,
    ( sK2(X0,X1) = sK3(X2)
    | sK4 != X2
    | sK4 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20732,c_12,c_11,c_1726])).

cnf(c_20757,plain,
    ( sK2(X0,X1) = sK3(X2)
    | sK4 != X0
    | sK4 != X2 ),
    inference(renaming,[status(thm)],[c_20756])).

cnf(c_20761,plain,
    ( sK2(sK4,X0) = sK3(X1)
    | sK4 != X1 ),
    inference(equality_resolution,[status(thm)],[c_20757])).

cnf(c_20961,plain,
    ( sK2(sK4,X0) = sK3(sK4) ),
    inference(equality_resolution,[status(thm)],[c_20761])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_tarski(X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19656,plain,
    ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK2(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19654,plain,
    ( k1_funct_1(sK2(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_21728,plain,
    ( k1_funct_1(sK2(X0,X1),X2) = X1
    | k4_xboole_0(X0,k2_tarski(X2,X2)) = X0 ),
    inference(superposition,[status(thm)],[c_19656,c_19654])).

cnf(c_22382,plain,
    ( k1_funct_1(sK3(sK4),X0) = X1
    | k4_xboole_0(sK4,k2_tarski(X0,X0)) = sK4 ),
    inference(superposition,[status(thm)],[c_20961,c_21728])).

cnf(c_10863,plain,
    ( X0 = X1
    | k1_relat_1(X0) != sK4
    | k1_relat_1(X1) != sK4
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11419,plain,
    ( sK2(X0,X1) = X2
    | k1_relat_1(X2) != sK4
    | sK4 != X0
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK2(X0,X1)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_10863])).

cnf(c_11651,plain,
    ( v1_funct_1(X2) != iProver_top
    | sK2(X0,X1) = X2
    | k1_relat_1(X2) != sK4
    | sK4 != X0
    | v1_relat_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11419,c_1864])).

cnf(c_11652,plain,
    ( sK2(X0,X1) = X2
    | k1_relat_1(X2) != sK4
    | sK4 != X0
    | v1_relat_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_11651])).

cnf(c_11661,plain,
    ( sK2(X0,X1) = sK3(X2)
    | sK4 != X2
    | sK4 != X0
    | v1_relat_1(sK3(X2)) != iProver_top
    | v1_funct_1(sK3(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_11652])).

cnf(c_11685,plain,
    ( sK2(X0,X1) = sK3(X2)
    | sK4 != X2
    | sK4 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11661,c_12,c_11,c_1726])).

cnf(c_11686,plain,
    ( sK2(X0,X1) = sK3(X2)
    | sK4 != X0
    | sK4 != X2 ),
    inference(renaming,[status(thm)],[c_11685])).

cnf(c_11690,plain,
    ( sK2(sK4,X0) = sK3(X1)
    | sK4 != X1 ),
    inference(equality_resolution,[status(thm)],[c_11686])).

cnf(c_11850,plain,
    ( sK2(sK4,X0) = sK3(sK4) ),
    inference(equality_resolution,[status(thm)],[c_11690])).

cnf(c_10871,plain,
    ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10869,plain,
    ( k1_funct_1(sK2(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_12411,plain,
    ( k1_funct_1(sK2(X0,X1),X2) = X1
    | k4_xboole_0(X0,k2_tarski(X2,X2)) = X0 ),
    inference(superposition,[status(thm)],[c_10871,c_10869])).

cnf(c_13333,plain,
    ( k1_funct_1(sK3(sK4),X0) = X1
    | k4_xboole_0(sK4,k2_tarski(X0,X0)) = sK4 ),
    inference(superposition,[status(thm)],[c_11850,c_12411])).

cnf(c_13536,plain,
    ( k1_funct_1(sK3(sK4),X0) != sK4
    | k4_xboole_0(sK4,k2_tarski(X0,X0)) = sK4 ),
    inference(equality_factoring,[status(thm)],[c_13333])).

cnf(c_13544,plain,
    ( k4_xboole_0(sK4,k2_tarski(X0,X0)) = sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13536,c_13333])).

cnf(c_22393,plain,
    ( k4_xboole_0(sK4,k2_tarski(X0,X0)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22382,c_13544])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_tarski(X0,X0)) != X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_19655,plain,
    ( k4_xboole_0(X0,k2_tarski(X1,X1)) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_22396,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_22393,c_19655])).

cnf(c_22749,plain,
    ( sK4 = X0
    | r2_hidden(sK0(sK4,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_19659,c_22396])).

cnf(c_22805,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK0(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_22749])).

cnf(c_2,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_19825,plain,
    ( k4_xboole_0(k1_xboole_0,k2_tarski(sK0(sK4,k1_xboole_0),sK0(sK4,k1_xboole_0))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_19816,plain,
    ( ~ r2_hidden(sK0(sK4,k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k2_tarski(sK0(sK4,k1_xboole_0),sK0(sK4,k1_xboole_0))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_19817,plain,
    ( k4_xboole_0(k1_xboole_0,k2_tarski(sK0(sK4,k1_xboole_0),sK0(sK4,k1_xboole_0))) != k1_xboole_0
    | r2_hidden(sK0(sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19816])).

cnf(c_197,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1119,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_1120,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1119])).

cnf(c_5,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_52,plain,
    ( r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_49,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22805,c_19825,c_19817,c_1120,c_52,c_49,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.54/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.54/1.50  
% 7.54/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.54/1.50  
% 7.54/1.50  ------  iProver source info
% 7.54/1.50  
% 7.54/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.54/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.54/1.50  git: non_committed_changes: false
% 7.54/1.50  git: last_make_outside_of_git: false
% 7.54/1.50  
% 7.54/1.50  ------ 
% 7.54/1.50  ------ Parsing...
% 7.54/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  ------ Proving...
% 7.54/1.50  ------ Problem Properties 
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  clauses                                 19
% 7.54/1.50  conjectures                             2
% 7.54/1.50  EPR                                     1
% 7.54/1.50  Horn                                    16
% 7.54/1.50  unary                                   9
% 7.54/1.50  binary                                  5
% 7.54/1.50  lits                                    38
% 7.54/1.50  lits eq                                 18
% 7.54/1.50  fd_pure                                 0
% 7.54/1.50  fd_pseudo                               0
% 7.54/1.50  fd_cond                                 0
% 7.54/1.50  fd_pseudo_cond                          5
% 7.54/1.50  AC symbols                              0
% 7.54/1.50  
% 7.54/1.50  ------ Input Options Time Limit: Unbounded
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing...
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 7.54/1.50  Current options:
% 7.54/1.50  ------ 
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing...
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  % SZS status Theorem for theBenchmark.p
% 7.54/1.50  
% 7.54/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.54/1.50  
% 7.54/1.50  fof(f1,axiom,(
% 7.54/1.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 7.54/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f10,plain,(
% 7.54/1.50    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 7.54/1.50    inference(ennf_transformation,[],[f1])).
% 7.54/1.50  
% 7.54/1.50  fof(f15,plain,(
% 7.54/1.50    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 7.54/1.50    inference(nnf_transformation,[],[f10])).
% 7.54/1.50  
% 7.54/1.50  fof(f16,plain,(
% 7.54/1.50    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 7.54/1.50    introduced(choice_axiom,[])).
% 7.54/1.50  
% 7.54/1.50  fof(f17,plain,(
% 7.54/1.50    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 7.54/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 7.54/1.50  
% 7.54/1.50  fof(f29,plain,(
% 7.54/1.50    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f17])).
% 7.54/1.50  
% 7.54/1.50  fof(f7,axiom,(
% 7.54/1.50    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.54/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f12,plain,(
% 7.54/1.50    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.54/1.50    inference(ennf_transformation,[],[f7])).
% 7.54/1.50  
% 7.54/1.50  fof(f25,plain,(
% 7.54/1.50    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 7.54/1.50    introduced(choice_axiom,[])).
% 7.54/1.50  
% 7.54/1.50  fof(f26,plain,(
% 7.54/1.50    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 7.54/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f25])).
% 7.54/1.50  
% 7.54/1.50  fof(f45,plain,(
% 7.54/1.50    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 7.54/1.50    inference(cnf_transformation,[],[f26])).
% 7.54/1.50  
% 7.54/1.50  fof(f6,axiom,(
% 7.54/1.50    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.54/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f11,plain,(
% 7.54/1.50    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.54/1.50    inference(ennf_transformation,[],[f6])).
% 7.54/1.50  
% 7.54/1.50  fof(f23,plain,(
% 7.54/1.50    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK2(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 7.54/1.50    introduced(choice_axiom,[])).
% 7.54/1.50  
% 7.54/1.50  fof(f24,plain,(
% 7.54/1.50    ! [X0,X1] : (! [X3] : (k1_funct_1(sK2(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1)))),
% 7.54/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f23])).
% 7.54/1.50  
% 7.54/1.50  fof(f41,plain,(
% 7.54/1.50    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0) )),
% 7.54/1.50    inference(cnf_transformation,[],[f24])).
% 7.54/1.50  
% 7.54/1.50  fof(f8,conjecture,(
% 7.54/1.50    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 7.54/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f9,negated_conjecture,(
% 7.54/1.50    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 7.54/1.50    inference(negated_conjecture,[],[f8])).
% 7.54/1.50  
% 7.54/1.50  fof(f13,plain,(
% 7.54/1.50    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 7.54/1.50    inference(ennf_transformation,[],[f9])).
% 7.54/1.50  
% 7.54/1.50  fof(f14,plain,(
% 7.54/1.50    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.54/1.50    inference(flattening,[],[f13])).
% 7.54/1.50  
% 7.54/1.50  fof(f27,plain,(
% 7.54/1.50    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK4 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK4 | k1_relat_1(X1) != sK4 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.54/1.50    introduced(choice_axiom,[])).
% 7.54/1.50  
% 7.54/1.50  fof(f28,plain,(
% 7.54/1.50    k1_xboole_0 != sK4 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK4 | k1_relat_1(X1) != sK4 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.54/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f27])).
% 7.54/1.50  
% 7.54/1.50  fof(f47,plain,(
% 7.54/1.50    ( ! [X2,X1] : (X1 = X2 | k1_relat_1(X2) != sK4 | k1_relat_1(X1) != sK4 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f28])).
% 7.54/1.50  
% 7.54/1.50  fof(f39,plain,(
% 7.54/1.50    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1))) )),
% 7.54/1.50    inference(cnf_transformation,[],[f24])).
% 7.54/1.50  
% 7.54/1.50  fof(f40,plain,(
% 7.54/1.50    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1))) )),
% 7.54/1.50    inference(cnf_transformation,[],[f24])).
% 7.54/1.50  
% 7.54/1.50  fof(f43,plain,(
% 7.54/1.50    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 7.54/1.50    inference(cnf_transformation,[],[f26])).
% 7.54/1.50  
% 7.54/1.50  fof(f44,plain,(
% 7.54/1.50    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 7.54/1.50    inference(cnf_transformation,[],[f26])).
% 7.54/1.50  
% 7.54/1.50  fof(f5,axiom,(
% 7.54/1.50    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 7.54/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f22,plain,(
% 7.54/1.50    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 7.54/1.50    inference(nnf_transformation,[],[f5])).
% 7.54/1.50  
% 7.54/1.50  fof(f38,plain,(
% 7.54/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f22])).
% 7.54/1.50  
% 7.54/1.50  fof(f4,axiom,(
% 7.54/1.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.54/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f36,plain,(
% 7.54/1.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f4])).
% 7.54/1.50  
% 7.54/1.50  fof(f53,plain,(
% 7.54/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k2_tarski(X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 7.54/1.50    inference(definition_unfolding,[],[f38,f36])).
% 7.54/1.50  
% 7.54/1.50  fof(f42,plain,(
% 7.54/1.50    ( ! [X0,X3,X1] : (k1_funct_1(sK2(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f24])).
% 7.54/1.50  
% 7.54/1.50  fof(f37,plain,(
% 7.54/1.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 7.54/1.50    inference(cnf_transformation,[],[f22])).
% 7.54/1.50  
% 7.54/1.50  fof(f54,plain,(
% 7.54/1.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0) )),
% 7.54/1.50    inference(definition_unfolding,[],[f37,f36])).
% 7.54/1.50  
% 7.54/1.50  fof(f2,axiom,(
% 7.54/1.50    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 7.54/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f31,plain,(
% 7.54/1.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f2])).
% 7.54/1.50  
% 7.54/1.50  fof(f3,axiom,(
% 7.54/1.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.54/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f18,plain,(
% 7.54/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.54/1.50    inference(nnf_transformation,[],[f3])).
% 7.54/1.50  
% 7.54/1.50  fof(f19,plain,(
% 7.54/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.54/1.50    inference(rectify,[],[f18])).
% 7.54/1.50  
% 7.54/1.50  fof(f20,plain,(
% 7.54/1.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 7.54/1.50    introduced(choice_axiom,[])).
% 7.54/1.50  
% 7.54/1.50  fof(f21,plain,(
% 7.54/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.54/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 7.54/1.50  
% 7.54/1.50  fof(f33,plain,(
% 7.54/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.54/1.50    inference(cnf_transformation,[],[f21])).
% 7.54/1.50  
% 7.54/1.50  fof(f51,plain,(
% 7.54/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 7.54/1.50    inference(definition_unfolding,[],[f33,f36])).
% 7.54/1.50  
% 7.54/1.50  fof(f55,plain,(
% 7.54/1.50    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 7.54/1.50    inference(equality_resolution,[],[f51])).
% 7.54/1.50  
% 7.54/1.50  fof(f56,plain,(
% 7.54/1.50    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 7.54/1.50    inference(equality_resolution,[],[f55])).
% 7.54/1.50  
% 7.54/1.50  fof(f32,plain,(
% 7.54/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.54/1.50    inference(cnf_transformation,[],[f21])).
% 7.54/1.50  
% 7.54/1.50  fof(f52,plain,(
% 7.54/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 7.54/1.50    inference(definition_unfolding,[],[f32,f36])).
% 7.54/1.50  
% 7.54/1.50  fof(f57,plain,(
% 7.54/1.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 7.54/1.50    inference(equality_resolution,[],[f52])).
% 7.54/1.50  
% 7.54/1.50  fof(f48,plain,(
% 7.54/1.50    k1_xboole_0 != sK4),
% 7.54/1.50    inference(cnf_transformation,[],[f28])).
% 7.54/1.50  
% 7.54/1.50  cnf(c_1,plain,
% 7.54/1.50      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 7.54/1.50      inference(cnf_transformation,[],[f29]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_19659,plain,
% 7.54/1.50      ( X0 = X1
% 7.54/1.50      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 7.54/1.50      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_14,plain,
% 7.54/1.50      ( k1_relat_1(sK3(X0)) = X0 ),
% 7.54/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_10,plain,
% 7.54/1.50      ( k1_relat_1(sK2(X0,X1)) = X0 ),
% 7.54/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_18,negated_conjecture,
% 7.54/1.50      ( ~ v1_relat_1(X0)
% 7.54/1.50      | ~ v1_relat_1(X1)
% 7.54/1.50      | ~ v1_funct_1(X0)
% 7.54/1.50      | ~ v1_funct_1(X1)
% 7.54/1.50      | X1 = X0
% 7.54/1.50      | k1_relat_1(X0) != sK4
% 7.54/1.50      | k1_relat_1(X1) != sK4 ),
% 7.54/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_19649,plain,
% 7.54/1.50      ( X0 = X1
% 7.54/1.50      | k1_relat_1(X0) != sK4
% 7.54/1.50      | k1_relat_1(X1) != sK4
% 7.54/1.50      | v1_relat_1(X1) != iProver_top
% 7.54/1.50      | v1_relat_1(X0) != iProver_top
% 7.54/1.50      | v1_funct_1(X1) != iProver_top
% 7.54/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_20259,plain,
% 7.54/1.50      ( sK2(X0,X1) = X2
% 7.54/1.50      | k1_relat_1(X2) != sK4
% 7.54/1.50      | sK4 != X0
% 7.54/1.50      | v1_relat_1(X2) != iProver_top
% 7.54/1.50      | v1_relat_1(sK2(X0,X1)) != iProver_top
% 7.54/1.50      | v1_funct_1(X2) != iProver_top
% 7.54/1.50      | v1_funct_1(sK2(X0,X1)) != iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_10,c_19649]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_1284,plain,
% 7.54/1.50      ( X0 = X1
% 7.54/1.50      | k1_relat_1(X0) != sK4
% 7.54/1.50      | k1_relat_1(X1) != sK4
% 7.54/1.50      | v1_relat_1(X1) != iProver_top
% 7.54/1.50      | v1_relat_1(X0) != iProver_top
% 7.54/1.50      | v1_funct_1(X1) != iProver_top
% 7.54/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_1701,plain,
% 7.54/1.50      ( sK2(X0,X1) = X2
% 7.54/1.50      | k1_relat_1(X2) != sK4
% 7.54/1.50      | sK4 != X0
% 7.54/1.50      | v1_relat_1(X2) != iProver_top
% 7.54/1.50      | v1_relat_1(sK2(X0,X1)) != iProver_top
% 7.54/1.50      | v1_funct_1(X2) != iProver_top
% 7.54/1.50      | v1_funct_1(sK2(X0,X1)) != iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_10,c_1284]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_12,plain,
% 7.54/1.50      ( v1_relat_1(sK2(X0,X1)) ),
% 7.54/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_32,plain,
% 7.54/1.50      ( v1_relat_1(sK2(X0,X1)) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_11,plain,
% 7.54/1.50      ( v1_funct_1(sK2(X0,X1)) ),
% 7.54/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_35,plain,
% 7.54/1.50      ( v1_funct_1(sK2(X0,X1)) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_1863,plain,
% 7.54/1.50      ( v1_funct_1(X2) != iProver_top
% 7.54/1.50      | sK2(X0,X1) = X2
% 7.54/1.50      | k1_relat_1(X2) != sK4
% 7.54/1.50      | sK4 != X0
% 7.54/1.50      | v1_relat_1(X2) != iProver_top ),
% 7.54/1.50      inference(global_propositional_subsumption,
% 7.54/1.50                [status(thm)],
% 7.54/1.50                [c_1701,c_32,c_35]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_1864,plain,
% 7.54/1.50      ( sK2(X0,X1) = X2
% 7.54/1.50      | k1_relat_1(X2) != sK4
% 7.54/1.50      | sK4 != X0
% 7.54/1.50      | v1_relat_1(X2) != iProver_top
% 7.54/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.54/1.50      inference(renaming,[status(thm)],[c_1863]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_20722,plain,
% 7.54/1.50      ( v1_funct_1(X2) != iProver_top
% 7.54/1.50      | sK2(X0,X1) = X2
% 7.54/1.50      | k1_relat_1(X2) != sK4
% 7.54/1.50      | sK4 != X0
% 7.54/1.50      | v1_relat_1(X2) != iProver_top ),
% 7.54/1.50      inference(global_propositional_subsumption,
% 7.54/1.50                [status(thm)],
% 7.54/1.50                [c_20259,c_32,c_35,c_1701]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_20723,plain,
% 7.54/1.50      ( sK2(X0,X1) = X2
% 7.54/1.50      | k1_relat_1(X2) != sK4
% 7.54/1.50      | sK4 != X0
% 7.54/1.50      | v1_relat_1(X2) != iProver_top
% 7.54/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.54/1.50      inference(renaming,[status(thm)],[c_20722]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_20732,plain,
% 7.54/1.50      ( sK2(X0,X1) = sK3(X2)
% 7.54/1.50      | sK4 != X2
% 7.54/1.50      | sK4 != X0
% 7.54/1.50      | v1_relat_1(sK3(X2)) != iProver_top
% 7.54/1.50      | v1_funct_1(sK3(X2)) != iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_14,c_20723]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_1426,plain,
% 7.54/1.50      ( sK3(X0) = X1
% 7.54/1.50      | k1_relat_1(X1) != sK4
% 7.54/1.50      | sK4 != X0
% 7.54/1.50      | v1_relat_1(X1) != iProver_top
% 7.54/1.50      | v1_relat_1(sK3(X0)) != iProver_top
% 7.54/1.50      | v1_funct_1(X1) != iProver_top
% 7.54/1.50      | v1_funct_1(sK3(X0)) != iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_14,c_1284]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_16,plain,
% 7.54/1.50      ( v1_relat_1(sK3(X0)) ),
% 7.54/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_22,plain,
% 7.54/1.50      ( v1_relat_1(sK3(X0)) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_15,plain,
% 7.54/1.50      ( v1_funct_1(sK3(X0)) ),
% 7.54/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_25,plain,
% 7.54/1.50      ( v1_funct_1(sK3(X0)) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_1431,plain,
% 7.54/1.50      ( v1_funct_1(X1) != iProver_top
% 7.54/1.50      | sK3(X0) = X1
% 7.54/1.50      | k1_relat_1(X1) != sK4
% 7.54/1.50      | sK4 != X0
% 7.54/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.54/1.50      inference(global_propositional_subsumption,
% 7.54/1.50                [status(thm)],
% 7.54/1.50                [c_1426,c_22,c_25]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_1432,plain,
% 7.54/1.50      ( sK3(X0) = X1
% 7.54/1.50      | k1_relat_1(X1) != sK4
% 7.54/1.50      | sK4 != X0
% 7.54/1.50      | v1_relat_1(X1) != iProver_top
% 7.54/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.54/1.50      inference(renaming,[status(thm)],[c_1431]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_1700,plain,
% 7.54/1.50      ( sK2(X0,X1) = sK3(X2)
% 7.54/1.50      | sK4 != X0
% 7.54/1.50      | sK4 != X2
% 7.54/1.50      | v1_relat_1(sK2(X0,X1)) != iProver_top
% 7.54/1.50      | v1_funct_1(sK2(X0,X1)) != iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_10,c_1432]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_1726,plain,
% 7.54/1.50      ( ~ v1_relat_1(sK2(X0,X1))
% 7.54/1.50      | ~ v1_funct_1(sK2(X0,X1))
% 7.54/1.50      | sK2(X0,X1) = sK3(X2)
% 7.54/1.50      | sK4 != X0
% 7.54/1.50      | sK4 != X2 ),
% 7.54/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_1700]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_20756,plain,
% 7.54/1.50      ( sK2(X0,X1) = sK3(X2) | sK4 != X2 | sK4 != X0 ),
% 7.54/1.50      inference(global_propositional_subsumption,
% 7.54/1.50                [status(thm)],
% 7.54/1.50                [c_20732,c_12,c_11,c_1726]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_20757,plain,
% 7.54/1.50      ( sK2(X0,X1) = sK3(X2) | sK4 != X0 | sK4 != X2 ),
% 7.54/1.50      inference(renaming,[status(thm)],[c_20756]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_20761,plain,
% 7.54/1.50      ( sK2(sK4,X0) = sK3(X1) | sK4 != X1 ),
% 7.54/1.50      inference(equality_resolution,[status(thm)],[c_20757]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_20961,plain,
% 7.54/1.50      ( sK2(sK4,X0) = sK3(sK4) ),
% 7.54/1.50      inference(equality_resolution,[status(thm)],[c_20761]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7,plain,
% 7.54/1.50      ( r2_hidden(X0,X1) | k4_xboole_0(X1,k2_tarski(X0,X0)) = X1 ),
% 7.54/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_19656,plain,
% 7.54/1.50      ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
% 7.54/1.50      | r2_hidden(X1,X0) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_9,plain,
% 7.54/1.50      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK2(X1,X2),X0) = X2 ),
% 7.54/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_19654,plain,
% 7.54/1.50      ( k1_funct_1(sK2(X0,X1),X2) = X1
% 7.54/1.50      | r2_hidden(X2,X0) != iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_21728,plain,
% 7.54/1.50      ( k1_funct_1(sK2(X0,X1),X2) = X1
% 7.54/1.50      | k4_xboole_0(X0,k2_tarski(X2,X2)) = X0 ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_19656,c_19654]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_22382,plain,
% 7.54/1.50      ( k1_funct_1(sK3(sK4),X0) = X1
% 7.54/1.50      | k4_xboole_0(sK4,k2_tarski(X0,X0)) = sK4 ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_20961,c_21728]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_10863,plain,
% 7.54/1.50      ( X0 = X1
% 7.54/1.50      | k1_relat_1(X0) != sK4
% 7.54/1.50      | k1_relat_1(X1) != sK4
% 7.54/1.50      | v1_relat_1(X1) != iProver_top
% 7.54/1.50      | v1_relat_1(X0) != iProver_top
% 7.54/1.50      | v1_funct_1(X1) != iProver_top
% 7.54/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_11419,plain,
% 7.54/1.50      ( sK2(X0,X1) = X2
% 7.54/1.50      | k1_relat_1(X2) != sK4
% 7.54/1.50      | sK4 != X0
% 7.54/1.50      | v1_relat_1(X2) != iProver_top
% 7.54/1.50      | v1_relat_1(sK2(X0,X1)) != iProver_top
% 7.54/1.50      | v1_funct_1(X2) != iProver_top
% 7.54/1.50      | v1_funct_1(sK2(X0,X1)) != iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_10,c_10863]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_11651,plain,
% 7.54/1.50      ( v1_funct_1(X2) != iProver_top
% 7.54/1.50      | sK2(X0,X1) = X2
% 7.54/1.50      | k1_relat_1(X2) != sK4
% 7.54/1.50      | sK4 != X0
% 7.54/1.50      | v1_relat_1(X2) != iProver_top ),
% 7.54/1.50      inference(global_propositional_subsumption,
% 7.54/1.50                [status(thm)],
% 7.54/1.50                [c_11419,c_1864]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_11652,plain,
% 7.54/1.50      ( sK2(X0,X1) = X2
% 7.54/1.50      | k1_relat_1(X2) != sK4
% 7.54/1.50      | sK4 != X0
% 7.54/1.50      | v1_relat_1(X2) != iProver_top
% 7.54/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.54/1.50      inference(renaming,[status(thm)],[c_11651]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_11661,plain,
% 7.54/1.50      ( sK2(X0,X1) = sK3(X2)
% 7.54/1.50      | sK4 != X2
% 7.54/1.50      | sK4 != X0
% 7.54/1.50      | v1_relat_1(sK3(X2)) != iProver_top
% 7.54/1.50      | v1_funct_1(sK3(X2)) != iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_14,c_11652]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_11685,plain,
% 7.54/1.50      ( sK2(X0,X1) = sK3(X2) | sK4 != X2 | sK4 != X0 ),
% 7.54/1.50      inference(global_propositional_subsumption,
% 7.54/1.50                [status(thm)],
% 7.54/1.50                [c_11661,c_12,c_11,c_1726]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_11686,plain,
% 7.54/1.50      ( sK2(X0,X1) = sK3(X2) | sK4 != X0 | sK4 != X2 ),
% 7.54/1.50      inference(renaming,[status(thm)],[c_11685]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_11690,plain,
% 7.54/1.50      ( sK2(sK4,X0) = sK3(X1) | sK4 != X1 ),
% 7.54/1.50      inference(equality_resolution,[status(thm)],[c_11686]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_11850,plain,
% 7.54/1.50      ( sK2(sK4,X0) = sK3(sK4) ),
% 7.54/1.50      inference(equality_resolution,[status(thm)],[c_11690]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_10871,plain,
% 7.54/1.50      ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
% 7.54/1.50      | r2_hidden(X1,X0) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_10869,plain,
% 7.54/1.50      ( k1_funct_1(sK2(X0,X1),X2) = X1
% 7.54/1.50      | r2_hidden(X2,X0) != iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_12411,plain,
% 7.54/1.50      ( k1_funct_1(sK2(X0,X1),X2) = X1
% 7.54/1.50      | k4_xboole_0(X0,k2_tarski(X2,X2)) = X0 ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_10871,c_10869]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_13333,plain,
% 7.54/1.50      ( k1_funct_1(sK3(sK4),X0) = X1
% 7.54/1.50      | k4_xboole_0(sK4,k2_tarski(X0,X0)) = sK4 ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_11850,c_12411]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_13536,plain,
% 7.54/1.50      ( k1_funct_1(sK3(sK4),X0) != sK4
% 7.54/1.50      | k4_xboole_0(sK4,k2_tarski(X0,X0)) = sK4 ),
% 7.54/1.50      inference(equality_factoring,[status(thm)],[c_13333]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_13544,plain,
% 7.54/1.50      ( k4_xboole_0(sK4,k2_tarski(X0,X0)) = sK4 ),
% 7.54/1.50      inference(forward_subsumption_resolution,
% 7.54/1.50                [status(thm)],
% 7.54/1.50                [c_13536,c_13333]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_22393,plain,
% 7.54/1.50      ( k4_xboole_0(sK4,k2_tarski(X0,X0)) = sK4 ),
% 7.54/1.50      inference(global_propositional_subsumption,
% 7.54/1.50                [status(thm)],
% 7.54/1.50                [c_22382,c_13544]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_8,plain,
% 7.54/1.50      ( ~ r2_hidden(X0,X1) | k4_xboole_0(X1,k2_tarski(X0,X0)) != X1 ),
% 7.54/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_19655,plain,
% 7.54/1.50      ( k4_xboole_0(X0,k2_tarski(X1,X1)) != X0
% 7.54/1.50      | r2_hidden(X1,X0) != iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_22396,plain,
% 7.54/1.50      ( r2_hidden(X0,sK4) != iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_22393,c_19655]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_22749,plain,
% 7.54/1.50      ( sK4 = X0 | r2_hidden(sK0(sK4,X0),X0) = iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_19659,c_22396]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_22805,plain,
% 7.54/1.50      ( sK4 = k1_xboole_0
% 7.54/1.50      | r2_hidden(sK0(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.54/1.50      inference(instantiation,[status(thm)],[c_22749]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_2,plain,
% 7.54/1.50      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.54/1.50      inference(cnf_transformation,[],[f31]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_19825,plain,
% 7.54/1.50      ( k4_xboole_0(k1_xboole_0,k2_tarski(sK0(sK4,k1_xboole_0),sK0(sK4,k1_xboole_0))) = k1_xboole_0 ),
% 7.54/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_19816,plain,
% 7.54/1.50      ( ~ r2_hidden(sK0(sK4,k1_xboole_0),k1_xboole_0)
% 7.54/1.50      | k4_xboole_0(k1_xboole_0,k2_tarski(sK0(sK4,k1_xboole_0),sK0(sK4,k1_xboole_0))) != k1_xboole_0 ),
% 7.54/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_19817,plain,
% 7.54/1.50      ( k4_xboole_0(k1_xboole_0,k2_tarski(sK0(sK4,k1_xboole_0),sK0(sK4,k1_xboole_0))) != k1_xboole_0
% 7.54/1.50      | r2_hidden(sK0(sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_19816]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_197,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_1119,plain,
% 7.54/1.50      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 7.54/1.50      inference(instantiation,[status(thm)],[c_197]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_1120,plain,
% 7.54/1.50      ( sK4 != k1_xboole_0
% 7.54/1.50      | k1_xboole_0 = sK4
% 7.54/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.54/1.50      inference(instantiation,[status(thm)],[c_1119]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_5,plain,
% 7.54/1.50      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 7.54/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_52,plain,
% 7.54/1.50      ( r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)) ),
% 7.54/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_6,plain,
% 7.54/1.50      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 7.54/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_49,plain,
% 7.54/1.50      ( ~ r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0))
% 7.54/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.54/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_17,negated_conjecture,
% 7.54/1.50      ( k1_xboole_0 != sK4 ),
% 7.54/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(contradiction,plain,
% 7.54/1.50      ( $false ),
% 7.54/1.50      inference(minisat,
% 7.54/1.50                [status(thm)],
% 7.54/1.50                [c_22805,c_19825,c_19817,c_1120,c_52,c_49,c_17]) ).
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.54/1.50  
% 7.54/1.50  ------                               Statistics
% 7.54/1.50  
% 7.54/1.50  ------ Selected
% 7.54/1.50  
% 7.54/1.50  total_time:                             0.731
% 7.54/1.50  
%------------------------------------------------------------------------------
