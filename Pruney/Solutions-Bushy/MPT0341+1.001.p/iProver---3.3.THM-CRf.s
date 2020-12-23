%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0341+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:03 EST 2020

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of clauses        :    3 (   3 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   15 (  15 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f9,f8])).

fof(f3,conjecture,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(ennf_transformation,[],[f4])).

fof(f6,plain,
    ( ? [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
   => ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).

fof(f10,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_0,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_1,negated_conjecture,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_20,plain,
    ( $false ),
    inference(resolution,[status(thm)],[c_0,c_1])).


%------------------------------------------------------------------------------
