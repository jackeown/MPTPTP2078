%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0616+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:43 EST 2020

% Result     : Theorem 0.84s
% Output     : CNFRefutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 186 expanded)
%              Number of clauses        :   29 (  44 expanded)
%              Number of leaves         :    7 (  37 expanded)
%              Depth                    :   17
%              Number of atoms          :  237 (1057 expanded)
%              Number of equality atoms :   66 ( 263 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( k1_funct_1(sK5,sK3) != sK4
        | ~ r2_hidden(sK3,k1_relat_1(sK5))
        | ~ r2_hidden(k4_tarski(sK3,sK4),sK5) )
      & ( ( k1_funct_1(sK5,sK3) = sK4
          & r2_hidden(sK3,k1_relat_1(sK5)) )
        | r2_hidden(k4_tarski(sK3,sK4),sK5) )
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ( k1_funct_1(sK5,sK3) != sK4
      | ~ r2_hidden(sK3,k1_relat_1(sK5))
      | ~ r2_hidden(k4_tarski(sK3,sK4),sK5) )
    & ( ( k1_funct_1(sK5,sK3) = sK4
        & r2_hidden(sK3,k1_relat_1(sK5)) )
      | r2_hidden(k4_tarski(sK3,sK4),sK5) )
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f17,f18])).

fof(f29,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f10])).

fof(f14,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14,f13,f12])).

fof(f25,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f28,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,
    ( k1_funct_1(sK5,sK3) = sK4
    | r2_hidden(k4_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f32,plain,
    ( k1_funct_1(sK5,sK3) != sK4
    | ~ r2_hidden(sK3,k1_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,
    ( r2_hidden(sK3,k1_relat_1(sK5))
    | r2_hidden(k4_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_11,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_77,plain,
    ( ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_6])).

cnf(c_78,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_77])).

cnf(c_182,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_78])).

cnf(c_183,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_182])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_187,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | k1_funct_1(sK5,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_183,c_12])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(k4_tarski(sK3,sK4),sK5)
    | k1_funct_1(sK5,sK3) = sK4 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_207,plain,
    ( k1_funct_1(sK5,sK3) = sK4 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_187,c_9])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_146,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_147,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_146])).

cnf(c_151,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
    | ~ r2_hidden(X0,k1_relat_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_147,c_12])).

cnf(c_152,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) ),
    inference(renaming,[status(thm)],[c_151])).

cnf(c_552,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_152])).

cnf(c_663,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK5) = iProver_top
    | r2_hidden(sK3,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_207,c_552])).

cnf(c_8,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK3,sK4),sK5)
    | ~ r2_hidden(sK3,k1_relat_1(sK5))
    | k1_funct_1(sK5,sK3) != sK4 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_246,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(sK3,sK4),sK5) ),
    inference(prop_impl,[status(thm)],[c_8,c_207])).

cnf(c_247,plain,
    ( ~ r2_hidden(k4_tarski(sK3,sK4),sK5)
    | ~ r2_hidden(sK3,k1_relat_1(sK5)) ),
    inference(renaming,[status(thm)],[c_246])).

cnf(c_549,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK5) != iProver_top
    | r2_hidden(sK3,k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_555,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(k4_tarski(sK3,sK4),sK5)
    | r2_hidden(sK3,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_553,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK5) = iProver_top
    | r2_hidden(sK3,k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_576,plain,
    ( r2_hidden(sK3,k1_relat_1(sK5)) = iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_555,c_553])).

cnf(c_581,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK5) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_549,c_576])).

cnf(c_15,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK5) = iProver_top
    | r2_hidden(sK3,k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_663,c_581,c_15])).


%------------------------------------------------------------------------------
