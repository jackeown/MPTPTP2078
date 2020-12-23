%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0933+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:57 EST 2020

% Result     : Theorem 31.60s
% Output     : CNFRefutation 31.60s
% Verified   : 
% Statistics : Number of formulae       :   36 (  87 expanded)
%              Number of clauses        :   19 (  23 expanded)
%              Number of leaves         :    4 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :   96 ( 429 expanded)
%              Number of equality atoms :   54 ( 225 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1413,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( k2_mcart_1(X0) = k2_mcart_1(X2)
            & k1_mcart_1(X0) = k1_mcart_1(X2)
            & r2_hidden(X0,X1)
            & r2_hidden(X2,X1) )
         => X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1414,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( ( k2_mcart_1(X0) = k2_mcart_1(X2)
              & k1_mcart_1(X0) = k1_mcart_1(X2)
              & r2_hidden(X0,X1)
              & r2_hidden(X2,X1) )
           => X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f1413])).

fof(f2846,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X0 != X2
          & k2_mcart_1(X0) = k2_mcart_1(X2)
          & k1_mcart_1(X0) = k1_mcart_1(X2)
          & r2_hidden(X0,X1)
          & r2_hidden(X2,X1) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1414])).

fof(f2847,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X0 != X2
          & k2_mcart_1(X0) = k2_mcart_1(X2)
          & k1_mcart_1(X0) = k1_mcart_1(X2)
          & r2_hidden(X0,X1)
          & r2_hidden(X2,X1) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f2846])).

fof(f3959,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X0 != X2
          & k2_mcart_1(X0) = k2_mcart_1(X2)
          & k1_mcart_1(X0) = k1_mcart_1(X2)
          & r2_hidden(X0,X1)
          & r2_hidden(X2,X1) )
     => ( sK460 != X0
        & k2_mcart_1(sK460) = k2_mcart_1(X0)
        & k1_mcart_1(sK460) = k1_mcart_1(X0)
        & r2_hidden(X0,X1)
        & r2_hidden(sK460,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f3958,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X0 != X2
            & k2_mcart_1(X0) = k2_mcart_1(X2)
            & k1_mcart_1(X0) = k1_mcart_1(X2)
            & r2_hidden(X0,X1)
            & r2_hidden(X2,X1) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( sK458 != X2
          & k2_mcart_1(sK458) = k2_mcart_1(X2)
          & k1_mcart_1(sK458) = k1_mcart_1(X2)
          & r2_hidden(sK458,sK459)
          & r2_hidden(X2,sK459) )
      & v1_relat_1(sK459) ) ),
    introduced(choice_axiom,[])).

fof(f3960,plain,
    ( sK458 != sK460
    & k2_mcart_1(sK458) = k2_mcart_1(sK460)
    & k1_mcart_1(sK458) = k1_mcart_1(sK460)
    & r2_hidden(sK458,sK459)
    & r2_hidden(sK460,sK459)
    & v1_relat_1(sK459) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK458,sK459,sK460])],[f2847,f3959,f3958])).

fof(f6512,plain,(
    r2_hidden(sK458,sK459) ),
    inference(cnf_transformation,[],[f3960])).

fof(f1338,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2768,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1338])).

fof(f2769,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2768])).

fof(f6301,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2769])).

fof(f6510,plain,(
    v1_relat_1(sK459) ),
    inference(cnf_transformation,[],[f3960])).

fof(f6511,plain,(
    r2_hidden(sK460,sK459) ),
    inference(cnf_transformation,[],[f3960])).

fof(f6514,plain,(
    k2_mcart_1(sK458) = k2_mcart_1(sK460) ),
    inference(cnf_transformation,[],[f3960])).

fof(f6513,plain,(
    k1_mcart_1(sK458) = k1_mcart_1(sK460) ),
    inference(cnf_transformation,[],[f3960])).

fof(f6515,plain,(
    sK458 != sK460 ),
    inference(cnf_transformation,[],[f3960])).

cnf(c_2527,negated_conjecture,
    ( r2_hidden(sK458,sK459) ),
    inference(cnf_transformation,[],[f6512])).

cnf(c_71650,plain,
    ( r2_hidden(sK458,sK459) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2527])).

cnf(c_2315,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6301])).

cnf(c_71799,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2315])).

cnf(c_99699,plain,
    ( k4_tarski(k1_mcart_1(sK458),k2_mcart_1(sK458)) = sK458
    | v1_relat_1(sK459) != iProver_top ),
    inference(superposition,[status(thm)],[c_71650,c_71799])).

cnf(c_2529,negated_conjecture,
    ( v1_relat_1(sK459) ),
    inference(cnf_transformation,[],[f6510])).

cnf(c_2533,plain,
    ( v1_relat_1(sK459) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2529])).

cnf(c_100852,plain,
    ( k4_tarski(k1_mcart_1(sK458),k2_mcart_1(sK458)) = sK458 ),
    inference(global_propositional_subsumption,[status(thm)],[c_99699,c_2533])).

cnf(c_2528,negated_conjecture,
    ( r2_hidden(sK460,sK459) ),
    inference(cnf_transformation,[],[f6511])).

cnf(c_71649,plain,
    ( r2_hidden(sK460,sK459) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2528])).

cnf(c_99700,plain,
    ( k4_tarski(k1_mcart_1(sK460),k2_mcart_1(sK460)) = sK460
    | v1_relat_1(sK459) != iProver_top ),
    inference(superposition,[status(thm)],[c_71649,c_71799])).

cnf(c_2525,negated_conjecture,
    ( k2_mcart_1(sK458) = k2_mcart_1(sK460) ),
    inference(cnf_transformation,[],[f6514])).

cnf(c_2526,negated_conjecture,
    ( k1_mcart_1(sK458) = k1_mcart_1(sK460) ),
    inference(cnf_transformation,[],[f6513])).

cnf(c_99744,plain,
    ( k4_tarski(k1_mcart_1(sK458),k2_mcart_1(sK458)) = sK460
    | v1_relat_1(sK459) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_99700,c_2525,c_2526])).

cnf(c_100318,plain,
    ( k4_tarski(k1_mcart_1(sK458),k2_mcart_1(sK458)) = sK460 ),
    inference(global_propositional_subsumption,[status(thm)],[c_99744,c_2533])).

cnf(c_100855,plain,
    ( sK460 = sK458 ),
    inference(demodulation,[status(thm)],[c_100852,c_100318])).

cnf(c_2524,negated_conjecture,
    ( sK458 != sK460 ),
    inference(cnf_transformation,[],[f6515])).

cnf(c_100881,plain,
    ( sK458 != sK458 ),
    inference(demodulation,[status(thm)],[c_100855,c_2524])).

cnf(c_100882,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_100881])).

%------------------------------------------------------------------------------
