%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0468+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:40 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   24 (  46 expanded)
%              Number of clauses        :   13 (  20 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 ( 103 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t56_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(c_0_5,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X15,X16)
      | v1_xboole_0(X16)
      | r2_hidden(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_6,plain,(
    ! [X13] : m1_subset_1(esk4_1(X13),X13) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
         => X1 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t56_relat_1])).

fof(c_0_8,plain,(
    ! [X17] :
      ( ~ v1_xboole_0(X17)
      | X17 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_9,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X5,X6,X9,X11,X12] :
      ( ( ~ v1_relat_1(X5)
        | ~ r2_hidden(X6,X5)
        | X6 = k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)) )
      & ( r2_hidden(esk3_1(X9),X9)
        | v1_relat_1(X9) )
      & ( esk3_1(X9) != k4_tarski(X11,X12)
        | v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_12,negated_conjecture,(
    ! [X19,X20] :
      ( v1_relat_1(esk5_0)
      & ~ r2_hidden(k4_tarski(X19,X20),esk5_0)
      & esk5_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk4_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( X2 = k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( k4_tarski(esk1_2(esk5_0,X1),esk2_2(esk5_0,X1)) = X1
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk4_1(esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,X2),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( k4_tarski(esk1_2(esk5_0,esk4_1(esk5_0)),esk2_2(esk5_0,esk4_1(esk5_0))) = esk4_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_20])]),
    [proof]).

%------------------------------------------------------------------------------
