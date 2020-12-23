%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0438+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:38 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   25 (  50 expanded)
%              Number of clauses        :   14 (  20 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   89 ( 155 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    inference(assume_negation,[status(cth)],[t21_relat_1])).

fof(c_0_6,plain,(
    ! [X23,X24,X25,X27,X28,X29,X30,X32] :
      ( ( ~ r2_hidden(X25,X24)
        | r2_hidden(k4_tarski(esk6_3(X23,X24,X25),X25),X23)
        | X24 != k2_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(X28,X27),X23)
        | r2_hidden(X27,X24)
        | X24 != k2_relat_1(X23) )
      & ( ~ r2_hidden(esk7_2(X29,X30),X30)
        | ~ r2_hidden(k4_tarski(X32,esk7_2(X29,X30)),X29)
        | X30 = k2_relat_1(X29) )
      & ( r2_hidden(esk7_2(X29,X30),X30)
        | r2_hidden(k4_tarski(esk8_2(X29,X30),esk7_2(X29,X30)),X29)
        | X30 = k2_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & ~ r1_tarski(esk9_0,k2_zfmisc_1(k1_relat_1(esk9_0),k2_relat_1(esk9_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(k4_tarski(X7,X8),X5)
        | r2_hidden(k4_tarski(X7,X8),X6)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(esk1_2(X5,X9),esk2_2(X5,X9)),X5)
        | r1_tarski(X5,X9)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X5,X9),esk2_2(X5,X9)),X9)
        | r1_tarski(X5,X9)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_9,plain,(
    ! [X12,X13,X14,X16,X17,X18,X19,X21] :
      ( ( ~ r2_hidden(X14,X13)
        | r2_hidden(k4_tarski(X14,esk3_3(X12,X13,X14)),X12)
        | X13 != k1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(X16,X17),X12)
        | r2_hidden(X16,X13)
        | X13 != k1_relat_1(X12) )
      & ( ~ r2_hidden(esk4_2(X18,X19),X19)
        | ~ r2_hidden(k4_tarski(esk4_2(X18,X19),X21),X18)
        | X19 = k1_relat_1(X18) )
      & ( r2_hidden(esk4_2(X18,X19),X19)
        | r2_hidden(k4_tarski(esk4_2(X18,X19),esk5_2(X18,X19)),X18)
        | X19 = k1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_10,plain,(
    ! [X34,X35,X36,X37] :
      ( ( r2_hidden(X34,X36)
        | ~ r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37)) )
      & ( r2_hidden(X35,X37)
        | ~ r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37)) )
      & ( ~ r2_hidden(X34,X36)
        | ~ r2_hidden(X35,X37)
        | r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_tarski(esk9_0,k2_zfmisc_1(k1_relat_1(esk9_0),k2_relat_1(esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk9_0,k2_zfmisc_1(k1_relat_1(esk9_0),k2_relat_1(esk9_0))),esk2_2(esk9_0,k2_zfmisc_1(k1_relat_1(esk9_0),k2_relat_1(esk9_0)))),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(esk2_2(X1,k2_zfmisc_1(X2,X3)),X3)
    | ~ r2_hidden(esk1_2(X1,k2_zfmisc_1(X2,X3)),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_2(esk9_0,k2_zfmisc_1(k1_relat_1(esk9_0),k2_relat_1(esk9_0))),k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,k2_zfmisc_1(k1_relat_1(esk9_0),k2_relat_1(esk9_0))),k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_14])]),c_0_12]),
    [proof]).

%------------------------------------------------------------------------------
