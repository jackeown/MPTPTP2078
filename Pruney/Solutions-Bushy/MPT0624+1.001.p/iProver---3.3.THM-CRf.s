%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0624+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:45 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 117 expanded)
%              Number of clauses        :   26 (  31 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :   16
%              Number of atoms          :  223 ( 543 expanded)
%              Number of equality atoms :   63 ( 119 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( k1_funct_1(X1,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X1)) )
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ! [X2] :
              ~ ( ! [X3] :
                    ~ ( k1_funct_1(X1,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X1)) )
                & r2_hidden(X2,X0) )
         => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( ? [X3] :
              ( k1_funct_1(X1,X3) = X2
              & r2_hidden(X3,k1_relat_1(X1)) )
          | ~ r2_hidden(X2,X0) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( ? [X3] :
              ( k1_funct_1(X1,X3) = X2
              & r2_hidden(X3,k1_relat_1(X1)) )
          | ~ r2_hidden(X2,X0) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f20,plain,(
    ! [X1,X2] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X2
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK6(X2)) = X2
        & r2_hidden(sK6(X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k2_relat_1(X1))
        & ! [X2] :
            ( ? [X3] :
                ( k1_funct_1(X1,X3) = X2
                & r2_hidden(X3,k1_relat_1(X1)) )
            | ~ r2_hidden(X2,X0) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK4,k2_relat_1(sK5))
      & ! [X2] :
          ( ? [X3] :
              ( k1_funct_1(sK5,X3) = X2
              & r2_hidden(X3,k1_relat_1(sK5)) )
          | ~ r2_hidden(X2,sK4) )
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ r1_tarski(sK4,k2_relat_1(sK5))
    & ! [X2] :
        ( ( k1_funct_1(sK5,sK6(X2)) = X2
          & r2_hidden(sK6(X2),k1_relat_1(sK5)) )
        | ~ r2_hidden(X2,sK4) )
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f10,f20,f19])).

fof(f34,plain,(
    ~ r1_tarski(sK4,k2_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X2] :
      ( k1_funct_1(sK5,sK6(X2)) = X2
      | ~ r2_hidden(X2,sK4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f17,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f17,f16,f15])).

fof(f26,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f36,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f31,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X2] :
      ( r2_hidden(sK6(X2),k1_relat_1(sK5))
      | ~ r2_hidden(X2,sK4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(sK4,k2_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_151,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k2_relat_1(sK5) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_152,plain,
    ( r2_hidden(sK0(sK4,k2_relat_1(sK5)),sK4) ),
    inference(unflattening,[status(thm)],[c_151])).

cnf(c_578,plain,
    ( r2_hidden(sK0(sK4,k2_relat_1(sK5)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_152])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | k1_funct_1(sK5,sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_580,plain,
    ( k1_funct_1(sK5,sK6(X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_665,plain,
    ( k1_funct_1(sK5,sK6(sK0(sK4,k2_relat_1(sK5)))) = sK0(sK4,k2_relat_1(sK5)) ),
    inference(superposition,[status(thm)],[c_578,c_580])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_11,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_247,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_248,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_252,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
    | ~ r2_hidden(X0,k1_relat_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_248,c_12])).

cnf(c_253,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) ),
    inference(renaming,[status(thm)],[c_252])).

cnf(c_572,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_830,plain,
    ( r2_hidden(sK0(sK4,k2_relat_1(sK5)),k2_relat_1(sK5)) = iProver_top
    | r2_hidden(sK6(sK0(sK4,k2_relat_1(sK5))),k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_665,c_572])).

cnf(c_10,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(sK6(X0),k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_647,plain,
    ( ~ r2_hidden(sK0(sK4,k2_relat_1(sK5)),sK4)
    | r2_hidden(sK6(sK0(sK4,k2_relat_1(sK5))),k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_648,plain,
    ( r2_hidden(sK0(sK4,k2_relat_1(sK5)),sK4) != iProver_top
    | r2_hidden(sK6(sK0(sK4,k2_relat_1(sK5))),k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_158,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k2_relat_1(sK5) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_159,plain,
    ( ~ r2_hidden(sK0(sK4,k2_relat_1(sK5)),k2_relat_1(sK5)) ),
    inference(unflattening,[status(thm)],[c_158])).

cnf(c_160,plain,
    ( r2_hidden(sK0(sK4,k2_relat_1(sK5)),k2_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_153,plain,
    ( r2_hidden(sK0(sK4,k2_relat_1(sK5)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_152])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_830,c_648,c_160,c_153])).


%------------------------------------------------------------------------------
