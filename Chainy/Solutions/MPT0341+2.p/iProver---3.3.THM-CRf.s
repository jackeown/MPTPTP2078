%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0341+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:36 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :   20 (  22 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f459,conjecture,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f460,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(negated_conjecture,[],[f459])).

fof(f700,plain,(
    ? [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(ennf_transformation,[],[f460])).

fof(f910,plain,
    ( ? [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
   => ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK66)) ),
    introduced(choice_axiom,[])).

fof(f911,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK66)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK66])],[f700,f910])).

fof(f1580,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK66)) ),
    inference(cnf_transformation,[],[f911])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f919,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1996,plain,(
    ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK66)) ),
    inference(definition_unfolding,[],[f1580,f919])).

fof(f452,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1572,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f452])).

fof(f451,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1571,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f451])).

fof(f1591,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f1571,f919])).

fof(f1994,plain,(
    ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f1572,f1591])).

cnf(c_655,negated_conjecture,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK66)) ),
    inference(cnf_transformation,[],[f1996])).

cnf(c_15105,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK66)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_647,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1994])).

cnf(c_15112,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_15558,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15105,c_15112])).

%------------------------------------------------------------------------------
