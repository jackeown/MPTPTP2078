%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0542+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:46 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   21 (  30 expanded)
%              Number of clauses        :   12 (  13 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   84 ( 107 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t144_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(d13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2)) ) ),
    inference(assume_negation,[status(cth)],[t144_relat_1])).

fof(c_0_5,plain,(
    ! [X6,X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(k4_tarski(esk1_4(X6,X7,X8,X9),X9),X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(X12,X11),X6)
        | ~ r2_hidden(X12,X7)
        | r2_hidden(X11,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(esk2_3(X6,X13,X14),X14)
        | ~ r2_hidden(k4_tarski(X16,esk2_3(X6,X13,X14)),X6)
        | ~ r2_hidden(X16,X13)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk3_3(X6,X13,X14),esk2_3(X6,X13,X14)),X6)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),X13)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & ~ r1_tarski(k9_relat_1(esk9_0,esk8_0),k2_relat_1(esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( ~ r1_tarski(X18,X19)
        | ~ r2_hidden(X20,X18)
        | r2_hidden(X20,X19) )
      & ( r2_hidden(esk4_2(X21,X22),X21)
        | r1_tarski(X21,X22) )
      & ( ~ r2_hidden(esk4_2(X21,X22),X22)
        | r1_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_8,plain,(
    ! [X24,X25,X26,X28,X29,X30,X31,X33] :
      ( ( ~ r2_hidden(X26,X25)
        | r2_hidden(k4_tarski(esk5_3(X24,X25,X26),X26),X24)
        | X25 != k2_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X29,X28),X24)
        | r2_hidden(X28,X25)
        | X25 != k2_relat_1(X24) )
      & ( ~ r2_hidden(esk6_2(X30,X31),X31)
        | ~ r2_hidden(k4_tarski(X33,esk6_2(X30,X31)),X30)
        | X31 = k2_relat_1(X30) )
      & ( r2_hidden(esk6_2(X30,X31),X31)
        | r2_hidden(k4_tarski(esk7_2(X30,X31),esk6_2(X30,X31)),X30)
        | X31 = k2_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(esk1_4(X1,X2,X3,X4),X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk9_0,esk8_0),k2_relat_1(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(esk1_4(X1,X2,k9_relat_1(X1,X2),X3),X3),X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(esk9_0,esk8_0),k2_relat_1(esk9_0)),k9_relat_1(esk9_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_4(esk9_0,esk8_0,k9_relat_1(esk9_0,esk8_0),esk4_2(k9_relat_1(esk9_0,esk8_0),k2_relat_1(esk9_0))),esk4_2(k9_relat_1(esk9_0,esk8_0),k2_relat_1(esk9_0))),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk4_2(k9_relat_1(esk9_0,esk8_0),k2_relat_1(esk9_0)),k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_10]),
    [proof]).

%------------------------------------------------------------------------------
