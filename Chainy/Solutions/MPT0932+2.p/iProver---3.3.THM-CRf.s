%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0932+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:57 EST 2020

% Result     : Theorem 43.39s
% Output     : CNFRefutation 43.39s
% Verified   : 
% Statistics : Number of formulae       :   34 (  75 expanded)
%              Number of clauses        :   17 (  21 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 213 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1412,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1413,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r2_hidden(X1,X0)
           => r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f1412])).

fof(f2844,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1)))
          & r2_hidden(X1,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1413])).

fof(f3956,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1)))
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(k2_mcart_1(sK459),k11_relat_1(X0,k1_mcart_1(sK459)))
        & r2_hidden(sK459,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3955,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1)))
            & r2_hidden(X1,X0) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r2_hidden(k2_mcart_1(X1),k11_relat_1(sK458,k1_mcart_1(X1)))
          & r2_hidden(X1,sK458) )
      & v1_relat_1(sK458) ) ),
    introduced(choice_axiom,[])).

fof(f3957,plain,
    ( ~ r2_hidden(k2_mcart_1(sK459),k11_relat_1(sK458,k1_mcart_1(sK459)))
    & r2_hidden(sK459,sK458)
    & v1_relat_1(sK458) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK458,sK459])],[f2844,f3956,f3955])).

fof(f6507,plain,(
    r2_hidden(sK459,sK458) ),
    inference(cnf_transformation,[],[f3957])).

fof(f1338,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2767,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1338])).

fof(f2768,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2767])).

fof(f6298,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2768])).

fof(f6506,plain,(
    v1_relat_1(sK458) ),
    inference(cnf_transformation,[],[f3957])).

fof(f808,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2061,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f808])).

fof(f3331,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f2061])).

fof(f5208,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f3331])).

fof(f6508,plain,(
    ~ r2_hidden(k2_mcart_1(sK459),k11_relat_1(sK458,k1_mcart_1(sK459))) ),
    inference(cnf_transformation,[],[f3957])).

cnf(c_2524,negated_conjecture,
    ( r2_hidden(sK459,sK458) ),
    inference(cnf_transformation,[],[f6507])).

cnf(c_71604,plain,
    ( r2_hidden(sK459,sK458) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2524])).

cnf(c_2315,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6298])).

cnf(c_71753,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2315])).

cnf(c_112027,plain,
    ( k4_tarski(k1_mcart_1(sK459),k2_mcart_1(sK459)) = sK459
    | v1_relat_1(sK458) != iProver_top ),
    inference(superposition,[status(thm)],[c_71604,c_71753])).

cnf(c_2525,negated_conjecture,
    ( v1_relat_1(sK458) ),
    inference(cnf_transformation,[],[f6506])).

cnf(c_104118,plain,
    ( ~ r2_hidden(sK459,sK458)
    | ~ v1_relat_1(sK458)
    | k4_tarski(k1_mcart_1(sK459),k2_mcart_1(sK459)) = sK459 ),
    inference(instantiation,[status(thm)],[c_2315])).

cnf(c_112627,plain,
    ( k4_tarski(k1_mcart_1(sK459),k2_mcart_1(sK459)) = sK459 ),
    inference(global_propositional_subsumption,[status(thm)],[c_112027,c_2525,c_2524,c_104118])).

cnf(c_1235,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f5208])).

cnf(c_72702,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1235])).

cnf(c_151499,plain,
    ( r2_hidden(k2_mcart_1(sK459),k11_relat_1(X0,k1_mcart_1(sK459))) = iProver_top
    | r2_hidden(sK459,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_112627,c_72702])).

cnf(c_2523,negated_conjecture,
    ( ~ r2_hidden(k2_mcart_1(sK459),k11_relat_1(sK458,k1_mcart_1(sK459))) ),
    inference(cnf_transformation,[],[f6508])).

cnf(c_71605,plain,
    ( r2_hidden(k2_mcart_1(sK459),k11_relat_1(sK458,k1_mcart_1(sK459))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2523])).

cnf(c_152187,plain,
    ( r2_hidden(sK459,sK458) != iProver_top
    | v1_relat_1(sK458) != iProver_top ),
    inference(superposition,[status(thm)],[c_151499,c_71605])).

cnf(c_2530,plain,
    ( r2_hidden(sK459,sK458) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2524])).

cnf(c_2529,plain,
    ( v1_relat_1(sK458) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2525])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_152187,c_2530,c_2529])).

%------------------------------------------------------------------------------
