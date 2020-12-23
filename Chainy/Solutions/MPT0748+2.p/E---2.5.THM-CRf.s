%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0748+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:51 EST 2020

% Result     : Theorem 13.15s
% Output     : CNFRefutation 13.15s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_ordinal1)).

fof(s1_xboole_0__e3_53__ordinal1,axiom,(
    ! [X1] :
    ? [X2] :
    ! [X3] :
      ( r2_hidden(X3,X2)
    <=> ( r2_hidden(X3,X1)
        & v3_ordinal1(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

fof(t37_ordinal1,axiom,(
    ! [X1] :
      ~ ! [X2] :
          ( r2_hidden(X2,X1)
        <=> v3_ordinal1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_ordinal1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ~ ! [X2] :
            ( v3_ordinal1(X2)
           => r2_hidden(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t38_ordinal1])).

fof(c_0_4,plain,(
    ! [X3181,X3183,X3184] :
      ( ( r2_hidden(X3183,X3181)
        | ~ r2_hidden(X3183,esk226_1(X3181)) )
      & ( v3_ordinal1(X3183)
        | ~ r2_hidden(X3183,esk226_1(X3181)) )
      & ( ~ r2_hidden(X3184,X3181)
        | ~ v3_ordinal1(X3184)
        | r2_hidden(X3184,esk226_1(X3181)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[s1_xboole_0__e3_53__ordinal1])])])])])])).

fof(c_0_5,plain,(
    ! [X3224] :
      ( ( ~ r2_hidden(esk232_1(X3224),X3224)
        | ~ v3_ordinal1(esk232_1(X3224)) )
      & ( r2_hidden(esk232_1(X3224),X3224)
        | v3_ordinal1(esk232_1(X3224)) ) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_ordinal1])])])).

fof(c_0_6,negated_conjecture,(
    ! [X3227] :
      ( ~ v3_ordinal1(X3227)
      | r2_hidden(X3227,esk233_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk226_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(esk232_1(X1),X1)
    | v3_ordinal1(esk232_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(X1,esk233_0)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v3_ordinal1(esk232_1(esk226_1(X1))) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,esk226_1(X2))
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk232_1(esk226_1(X1)),esk233_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(esk232_1(X1),X1)
    | ~ v3_ordinal1(esk232_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk232_1(esk226_1(X1)),esk226_1(esk233_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_10])])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_10])]),
    [proof]).
%------------------------------------------------------------------------------
