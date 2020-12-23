%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : ordinal1__t38_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:26 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   16 (  34 expanded)
%              Number of clauses        :    9 (  15 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  95 expanded)
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
    file('/export/starexec/sandbox2/benchmark/ordinal1__t38_ordinal1.p',t38_ordinal1)).

fof(s1_xboole_0__e3_53__ordinal1,axiom,(
    ! [X1] :
    ? [X2] :
    ! [X3] :
      ( r2_hidden(X3,X2)
    <=> ( r2_hidden(X3,X1)
        & v3_ordinal1(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t38_ordinal1.p',s1_xboole_0__e3_53__ordinal1)).

fof(t37_ordinal1,axiom,(
    ! [X1] :
      ~ ! [X2] :
          ( r2_hidden(X2,X1)
        <=> v3_ordinal1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t38_ordinal1.p',t37_ordinal1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ~ ! [X2] :
            ( v3_ordinal1(X2)
           => r2_hidden(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t38_ordinal1])).

fof(c_0_4,plain,(
    ! [X10,X12,X13] :
      ( ( r2_hidden(X12,X10)
        | ~ r2_hidden(X12,esk3_1(X10)) )
      & ( v3_ordinal1(X12)
        | ~ r2_hidden(X12,esk3_1(X10)) )
      & ( ~ r2_hidden(X13,X10)
        | ~ v3_ordinal1(X13)
        | r2_hidden(X13,esk3_1(X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[s1_xboole_0__e3_53__ordinal1])])])])])])).

fof(c_0_5,plain,(
    ! [X18] :
      ( ( ~ r2_hidden(esk4_1(X18),X18)
        | ~ v3_ordinal1(esk4_1(X18)) )
      & ( r2_hidden(esk4_1(X18),X18)
        | v3_ordinal1(esk4_1(X18)) ) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_ordinal1])])])).

fof(c_0_6,negated_conjecture,(
    ! [X5] :
      ( ~ v3_ordinal1(X5)
      | r2_hidden(X5,esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk3_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v3_ordinal1(esk4_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(X1,esk1_0)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v3_ordinal1(esk4_1(esk3_1(X1))) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,esk3_1(X2))
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk4_1(esk3_1(X1)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(esk4_1(X1),X1)
    | ~ v3_ordinal1(esk4_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk4_1(esk3_1(X1)),esk3_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_10])])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_10])]),
    [proof]).
%------------------------------------------------------------------------------
