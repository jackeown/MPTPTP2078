%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0341+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:43 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    4
%              Number of atoms          :   12 (  12 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    3 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_subset_1,conjecture,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(dt_k1_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(assume_negation,[status(cth)],[t4_subset_1])).

fof(c_0_4,plain,(
    ! [X1472] : m1_subset_1(k1_subset_1(X1472),k1_zfmisc_1(X1472)) ),
    inference(variable_rename,[status(thm)],[dt_k1_subset_1])).

fof(c_0_5,plain,(
    ! [X1471] : k1_subset_1(X1471) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_6,negated_conjecture,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(esk63_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(esk63_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10])]),
    [proof]).
%------------------------------------------------------------------------------
