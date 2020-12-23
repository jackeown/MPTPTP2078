%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0824+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:54 EST 2020

% Result     : Theorem 19.85s
% Output     : CNFRefutation 19.85s
% Verified   : 
% Statistics : Number of formulae       :   17 (  19 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    8
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1231,conjecture,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1232,negated_conjecture,(
    ~ ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(negated_conjecture,[],[f1231])).

fof(f2497,plain,(
    ? [X0,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(ennf_transformation,[],[f1232])).

fof(f3375,plain,
    ( ? [X0,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
   => ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK324,sK325))) ),
    introduced(choice_axiom,[])).

fof(f3376,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK324,sK325))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK324,sK325])],[f2497,f3375])).

fof(f5499,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK324,sK325))) ),
    inference(cnf_transformation,[],[f3376])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3386,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6194,plain,(
    ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK324,sK325))) ),
    inference(definition_unfolding,[],[f5499,f3386])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4206,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f5952,plain,(
    ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f4206,f3386])).

cnf(c_2105,negated_conjecture,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK324,sK325))) ),
    inference(cnf_transformation,[],[f6194])).

cnf(c_59694,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK324,sK325))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2105])).

cnf(c_813,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5952])).

cnf(c_60814,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_813])).

cnf(c_61640,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_59694,c_60814])).

%------------------------------------------------------------------------------
