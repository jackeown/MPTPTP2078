%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0969+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:58 EST 2020

% Result     : Theorem 39.45s
% Output     : CNFRefutation 39.45s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 232 expanded)
%              Number of clauses        :   25 (  57 expanded)
%              Number of leaves         :    6 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  146 ( 751 expanded)
%              Number of equality atoms :   69 ( 170 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1479,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2991,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1479])).

fof(f2992,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f2991])).

fof(f6991,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2992])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4246,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7993,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | o_0_0_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f6991,f4246])).

fof(f8337,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,k1_funct_2(o_0_0_xboole_0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
      | ~ v1_funct_2(X2,o_0_0_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f7993])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3205,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f3206,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f3205])).

fof(f4702,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f3206])).

fof(f7310,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f4702,f4246,f4246])).

fof(f8078,plain,(
    ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1) ),
    inference(equality_resolution,[],[f7310])).

fof(f376,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4781,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f7358,plain,(
    k1_tarski(o_0_0_xboole_0) = k1_zfmisc_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f4781,f4246,f4246])).

fof(f1480,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => r2_hidden(X1,k1_funct_2(X0,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1481,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => r2_hidden(X1,k1_funct_2(X0,X0)) ) ),
    inference(negated_conjecture,[],[f1480])).

fof(f2993,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,k1_funct_2(X0,X0))
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1481])).

fof(f2994,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,k1_funct_2(X0,X0))
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f2993])).

fof(f4235,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X1,k1_funct_2(X0,X0))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ~ r2_hidden(sK519,k1_funct_2(sK518,sK518))
      & m1_subset_1(sK519,k1_zfmisc_1(k2_zfmisc_1(sK518,sK518)))
      & v1_funct_2(sK519,sK518,sK518)
      & v1_funct_1(sK519) ) ),
    introduced(choice_axiom,[])).

fof(f4236,plain,
    ( ~ r2_hidden(sK519,k1_funct_2(sK518,sK518))
    & m1_subset_1(sK519,k1_zfmisc_1(k2_zfmisc_1(sK518,sK518)))
    & v1_funct_2(sK519,sK518,sK518)
    & v1_funct_1(sK519) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK518,sK519])],[f2994,f4235])).

fof(f6994,plain,(
    m1_subset_1(sK519,k1_zfmisc_1(k2_zfmisc_1(sK518,sK518))) ),
    inference(cnf_transformation,[],[f4236])).

fof(f6990,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2992])).

fof(f7994,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f6990,f4246])).

fof(f6992,plain,(
    v1_funct_1(sK519) ),
    inference(cnf_transformation,[],[f4236])).

fof(f6993,plain,(
    v1_funct_2(sK519,sK518,sK518) ),
    inference(cnf_transformation,[],[f4236])).

fof(f6995,plain,(
    ~ r2_hidden(sK519,k1_funct_2(sK518,sK518)) ),
    inference(cnf_transformation,[],[f4236])).

cnf(c_2728,plain,
    ( ~ v1_funct_2(X0,o_0_0_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
    | r2_hidden(X0,k1_funct_2(o_0_0_xboole_0,X1))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f8337])).

cnf(c_78706,plain,
    ( v1_funct_2(X0,o_0_0_xboole_0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))) != iProver_top
    | r2_hidden(X0,k1_funct_2(o_0_0_xboole_0,X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2728])).

cnf(c_451,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f8078])).

cnf(c_530,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = k1_tarski(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f7358])).

cnf(c_89181,plain,
    ( v1_funct_2(X0,o_0_0_xboole_0,X1) != iProver_top
    | m1_subset_1(X0,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | r2_hidden(X0,k1_funct_2(o_0_0_xboole_0,X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_78706,c_451,c_530])).

cnf(c_2731,negated_conjecture,
    ( m1_subset_1(sK519,k1_zfmisc_1(k2_zfmisc_1(sK518,sK518))) ),
    inference(cnf_transformation,[],[f6994])).

cnf(c_78703,plain,
    ( m1_subset_1(sK519,k1_zfmisc_1(k2_zfmisc_1(sK518,sK518))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2731])).

cnf(c_2729,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X0,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f7994])).

cnf(c_78705,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X1,k1_funct_2(X2,X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2729])).

cnf(c_125002,plain,
    ( sK518 = o_0_0_xboole_0
    | v1_funct_2(sK519,sK518,sK518) != iProver_top
    | r2_hidden(sK519,k1_funct_2(sK518,sK518)) = iProver_top
    | v1_funct_1(sK519) != iProver_top ),
    inference(superposition,[status(thm)],[c_78703,c_78705])).

cnf(c_2733,negated_conjecture,
    ( v1_funct_1(sK519) ),
    inference(cnf_transformation,[],[f6992])).

cnf(c_2760,plain,
    ( v1_funct_1(sK519) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2733])).

cnf(c_2732,negated_conjecture,
    ( v1_funct_2(sK519,sK518,sK518) ),
    inference(cnf_transformation,[],[f6993])).

cnf(c_2761,plain,
    ( v1_funct_2(sK519,sK518,sK518) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2732])).

cnf(c_2730,negated_conjecture,
    ( ~ r2_hidden(sK519,k1_funct_2(sK518,sK518)) ),
    inference(cnf_transformation,[],[f6995])).

cnf(c_2763,plain,
    ( r2_hidden(sK519,k1_funct_2(sK518,sK518)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2730])).

cnf(c_125578,plain,
    ( sK518 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_125002,c_2760,c_2761,c_2763])).

cnf(c_78704,plain,
    ( r2_hidden(sK519,k1_funct_2(sK518,sK518)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2730])).

cnf(c_125581,plain,
    ( r2_hidden(sK519,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_125578,c_78704])).

cnf(c_136628,plain,
    ( v1_funct_2(sK519,o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | m1_subset_1(sK519,k1_tarski(o_0_0_xboole_0)) != iProver_top
    | v1_funct_1(sK519) != iProver_top ),
    inference(superposition,[status(thm)],[c_89181,c_125581])).

cnf(c_125582,plain,
    ( m1_subset_1(sK519,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_125578,c_78703])).

cnf(c_125587,plain,
    ( m1_subset_1(sK519,k1_tarski(o_0_0_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_125582,c_451,c_530])).

cnf(c_78702,plain,
    ( v1_funct_2(sK519,sK518,sK518) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2732])).

cnf(c_125583,plain,
    ( v1_funct_2(sK519,o_0_0_xboole_0,o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_125578,c_78702])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_136628,c_125587,c_125583,c_2760])).

%------------------------------------------------------------------------------
