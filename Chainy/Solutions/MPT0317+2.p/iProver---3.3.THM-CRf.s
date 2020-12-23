%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0317+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:35 EST 2020

% Result     : Theorem 30.91s
% Output     : CNFRefutation 30.91s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 246 expanded)
%              Number of clauses        :   37 (  85 expanded)
%              Number of leaves         :    6 (  42 expanded)
%              Depth                    :   16
%              Number of atoms          :  199 ( 994 expanded)
%              Number of equality atoms :   90 ( 359 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f694,plain,(
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
    inference(nnf_transformation,[],[f175])).

fof(f695,plain,(
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
    inference(rectify,[],[f694])).

fof(f696,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK20(X0,X1) != X0
          | ~ r2_hidden(sK20(X0,X1),X1) )
        & ( sK20(X0,X1) = X0
          | r2_hidden(sK20(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f697,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK20(X0,X1) != X0
            | ~ r2_hidden(sK20(X0,X1),X1) )
          & ( sK20(X0,X1) = X0
            | r2_hidden(sK20(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f695,f696])).

fof(f1040,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f697])).

fof(f1815,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f1040])).

fof(f1816,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f1815])).

fof(f319,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f764,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f319])).

fof(f765,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f764])).

fof(f1255,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f765])).

fof(f339,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f340,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      <=> ( X1 = X3
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f339])).

fof(f573,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <~> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f340])).

fof(f773,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f573])).

fof(f774,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f773])).

fof(f775,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | ~ r2_hidden(X0,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
        & ( ( X1 = X3
            & r2_hidden(X0,X2) )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) )
   => ( ( sK51 != sK53
        | ~ r2_hidden(sK50,sK52)
        | ~ r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53))) )
      & ( ( sK51 = sK53
          & r2_hidden(sK50,sK52) )
        | r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53))) ) ) ),
    introduced(choice_axiom,[])).

fof(f776,plain,
    ( ( sK51 != sK53
      | ~ r2_hidden(sK50,sK52)
      | ~ r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53))) )
    & ( ( sK51 = sK53
        & r2_hidden(sK50,sK52) )
      | r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK50,sK51,sK52,sK53])],[f774,f775])).

fof(f1287,plain,
    ( sK51 = sK53
    | r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53))) ),
    inference(cnf_transformation,[],[f776])).

fof(f320,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
     => r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f559,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2))
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f320])).

fof(f1256,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2))
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f559])).

fof(f1288,plain,
    ( sK51 != sK53
    | ~ r2_hidden(sK50,sK52)
    | ~ r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53))) ),
    inference(cnf_transformation,[],[f776])).

fof(f1039,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f697])).

fof(f1817,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f1039])).

fof(f1253,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f765])).

fof(f1254,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f765])).

fof(f1286,plain,
    ( r2_hidden(sK50,sK52)
    | r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53))) ),
    inference(cnf_transformation,[],[f776])).

cnf(c_231,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1816])).

cnf(c_16883,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_231])).

cnf(c_433,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f1255])).

cnf(c_16783,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_467,negated_conjecture,
    ( r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53)))
    | sK51 = sK53 ),
    inference(cnf_transformation,[],[f1287])).

cnf(c_16753,plain,
    ( sK51 = sK53
    | r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_436,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) ),
    inference(cnf_transformation,[],[f1256])).

cnf(c_16769,plain,
    ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_57327,plain,
    ( sK53 = sK51
    | r2_hidden(k4_tarski(sK51,sK50),k2_zfmisc_1(k1_tarski(sK53),sK52)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16753,c_16769])).

cnf(c_466,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53)))
    | ~ r2_hidden(sK50,sK52)
    | sK51 != sK53 ),
    inference(cnf_transformation,[],[f1288])).

cnf(c_594,plain,
    ( sK51 != sK53
    | r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53))) != iProver_top
    | r2_hidden(sK50,sK52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_17994,plain,
    ( r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53)))
    | ~ r2_hidden(k4_tarski(sK51,sK50),k2_zfmisc_1(k1_tarski(sK53),sK52)) ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_17995,plain,
    ( r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53))) = iProver_top
    | r2_hidden(k4_tarski(sK51,sK50),k2_zfmisc_1(k1_tarski(sK53),sK52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17994])).

cnf(c_232,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f1817])).

cnf(c_18518,plain,
    ( ~ r2_hidden(sK51,k1_tarski(sK53))
    | sK51 = sK53 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_18519,plain,
    ( sK51 = sK53
    | r2_hidden(sK51,k1_tarski(sK53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18518])).

cnf(c_435,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f1253])).

cnf(c_19185,plain,
    ( ~ r2_hidden(k4_tarski(sK50,X0),k2_zfmisc_1(sK52,X1))
    | r2_hidden(sK50,sK52) ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_38288,plain,
    ( ~ r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53)))
    | r2_hidden(sK50,sK52) ),
    inference(instantiation,[status(thm)],[c_19185])).

cnf(c_38289,plain,
    ( r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53))) != iProver_top
    | r2_hidden(sK50,sK52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38288])).

cnf(c_434,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f1254])).

cnf(c_25405,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK51),k2_zfmisc_1(X1,k1_tarski(sK53)))
    | r2_hidden(sK51,k1_tarski(sK53)) ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_40358,plain,
    ( ~ r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53)))
    | r2_hidden(sK51,k1_tarski(sK53)) ),
    inference(instantiation,[status(thm)],[c_25405])).

cnf(c_40359,plain,
    ( r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53))) != iProver_top
    | r2_hidden(sK51,k1_tarski(sK53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40358])).

cnf(c_59889,plain,
    ( sK53 = sK51 ),
    inference(global_propositional_subsumption,[status(thm)],[c_57327,c_594,c_17995,c_18519,c_38289,c_40359])).

cnf(c_16754,plain,
    ( sK51 != sK53
    | r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53))) != iProver_top
    | r2_hidden(sK50,sK52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_59893,plain,
    ( sK51 != sK51
    | r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK51))) != iProver_top
    | r2_hidden(sK50,sK52) != iProver_top ),
    inference(demodulation,[status(thm)],[c_59889,c_16754])).

cnf(c_59894,plain,
    ( r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK51))) != iProver_top
    | r2_hidden(sK50,sK52) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_59893])).

cnf(c_468,negated_conjecture,
    ( r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53)))
    | r2_hidden(sK50,sK52) ),
    inference(cnf_transformation,[],[f1286])).

cnf(c_16752,plain,
    ( r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53))) = iProver_top
    | r2_hidden(sK50,sK52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_57326,plain,
    ( r2_hidden(k4_tarski(sK51,sK50),k2_zfmisc_1(k1_tarski(sK53),sK52)) = iProver_top
    | r2_hidden(sK50,sK52) = iProver_top ),
    inference(superposition,[status(thm)],[c_16752,c_16769])).

cnf(c_592,plain,
    ( r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK53))) = iProver_top
    | r2_hidden(sK50,sK52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_59898,plain,
    ( r2_hidden(sK50,sK52) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_57326,c_592,c_594,c_18519,c_38289,c_40359])).

cnf(c_60224,plain,
    ( r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(sK52,k1_tarski(sK51))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_59894,c_592,c_594,c_18519,c_38289,c_40359])).

cnf(c_103123,plain,
    ( r2_hidden(sK50,sK52) != iProver_top
    | r2_hidden(sK51,k1_tarski(sK51)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16783,c_60224])).

cnf(c_104426,plain,
    ( r2_hidden(sK51,k1_tarski(sK51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_103123,c_592,c_594,c_18519,c_38289,c_40359])).

cnf(c_104431,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_16883,c_104426])).

%------------------------------------------------------------------------------
