%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t18_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:56 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   15 (  18 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    3 (   4 expanded)
%              Depth                    :    5
%              Number of atoms          :   53 (  62 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t18_relat_1.p',d4_relat_1)).

fof(t18_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r2_hidden(X1,k1_relat_1(X2))
          & ! [X3] : ~ r2_hidden(X3,k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t18_relat_1.p',t18_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t18_relat_1.p',d5_relat_1)).

fof(c_0_3,plain,(
    ! [X10,X11,X12,X14,X15,X16,X17,X19] :
      ( ( ~ r2_hidden(X12,X11)
        | r2_hidden(k4_tarski(X12,esk3_3(X10,X11,X12)),X10)
        | X11 != k1_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(X14,X15),X10)
        | r2_hidden(X14,X11)
        | X11 != k1_relat_1(X10) )
      & ( ~ r2_hidden(esk4_2(X16,X17),X17)
        | ~ r2_hidden(k4_tarski(esk4_2(X16,X17),X19),X16)
        | X17 = k1_relat_1(X16) )
      & ( r2_hidden(esk4_2(X16,X17),X17)
        | r2_hidden(k4_tarski(esk4_2(X16,X17),esk5_2(X16,X17)),X16)
        | X17 = k1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ~ ( r2_hidden(X1,k1_relat_1(X2))
            & ! [X3] : ~ r2_hidden(X3,k2_relat_1(X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t18_relat_1])).

fof(c_0_5,plain,(
    ! [X21,X22,X23,X25,X26,X27,X28,X30] :
      ( ( ~ r2_hidden(X23,X22)
        | r2_hidden(k4_tarski(esk6_3(X21,X22,X23),X23),X21)
        | X22 != k2_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(X26,X25),X21)
        | r2_hidden(X25,X22)
        | X22 != k2_relat_1(X21) )
      & ( ~ r2_hidden(esk7_2(X27,X28),X28)
        | ~ r2_hidden(k4_tarski(X30,esk7_2(X27,X28)),X27)
        | X28 = k2_relat_1(X27) )
      & ( r2_hidden(esk7_2(X27,X28),X28)
        | r2_hidden(k4_tarski(esk8_2(X27,X28),esk7_2(X27,X28)),X27)
        | X28 = k2_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_7,negated_conjecture,(
    ! [X7] :
      ( v1_relat_1(esk2_0)
      & r2_hidden(esk1_0,k1_relat_1(esk2_0))
      & ~ r2_hidden(X7,k2_relat_1(esk2_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk3_3(esk2_0,k1_relat_1(esk2_0),esk1_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
