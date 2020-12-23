%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0748+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:08 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   19 (  58 expanded)
%              Number of clauses        :   12 (  26 expanded)
%              Number of leaves         :    3 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 ( 154 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_ordinal1,conjecture,(
    ! [X1] :
      ~ ! [X2] :
          ( v3_ordinal1(X2)
         => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_ordinal1)).

fof(t37_ordinal1,axiom,(
    ! [X1] :
      ~ ! [X2] :
          ( r2_hidden(X2,X1)
        <=> v3_ordinal1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_ordinal1)).

fof(s1_xboole_0__e3_53__ordinal1,axiom,(
    ! [X1] :
    ? [X2] :
    ! [X3] :
      ( r2_hidden(X3,X2)
    <=> ( r2_hidden(X3,X1)
        & v3_ordinal1(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ~ ! [X2] :
            ( v3_ordinal1(X2)
           => r2_hidden(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t38_ordinal1])).

fof(c_0_4,negated_conjecture,(
    ! [X11] :
      ( ~ v3_ordinal1(X11)
      | r2_hidden(X11,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X8] :
      ( ( ~ r2_hidden(esk2_1(X8),X8)
        | ~ v3_ordinal1(esk2_1(X8)) )
      & ( r2_hidden(esk2_1(X8),X8)
        | v3_ordinal1(esk2_1(X8)) ) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_ordinal1])])])).

fof(c_0_6,plain,(
    ! [X4,X6,X7] :
      ( ( r2_hidden(X6,X4)
        | ~ r2_hidden(X6,esk1_1(X4)) )
      & ( v3_ordinal1(X6)
        | ~ r2_hidden(X6,esk1_1(X4)) )
      & ( ~ r2_hidden(X7,X4)
        | ~ v3_ordinal1(X7)
        | r2_hidden(X7,esk1_1(X4)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[s1_xboole_0__e3_53__ordinal1])])])])])])).

cnf(c_0_7,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v3_ordinal1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,esk1_1(X2))
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk1_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk2_1(X1),esk3_0)
    | r2_hidden(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(esk2_1(X1),esk1_1(X2))
    | r2_hidden(esk2_1(X1),X1)
    | ~ r2_hidden(esk2_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk2_1(esk1_1(X1)),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk2_1(esk1_1(X1)),esk1_1(esk3_0))
    | r2_hidden(esk2_1(esk1_1(X1)),esk1_1(X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk2_1(esk1_1(esk3_0)),esk1_1(esk3_0)) ),
    inference(ef,[status(thm)],[c_0_14])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(esk2_1(X1),X1)
    | ~ v3_ordinal1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( v3_ordinal1(esk2_1(esk1_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_15])]),
    [proof]).

%------------------------------------------------------------------------------
