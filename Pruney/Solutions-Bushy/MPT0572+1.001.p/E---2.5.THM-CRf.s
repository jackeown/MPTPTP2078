%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0572+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:50 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 111 expanded)
%              Number of clauses        :   26 (  50 expanded)
%              Number of leaves         :    4 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  130 ( 478 expanded)
%              Number of equality atoms :   20 (  72 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t176_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k10_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k10_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))) ) ),
    inference(assume_negation,[status(cth)],[t176_relat_1])).

fof(c_0_5,plain,(
    ! [X6,X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(k4_tarski(X9,esk1_4(X6,X7,X8,X9)),X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(X11,X12),X6)
        | ~ r2_hidden(X12,X7)
        | r2_hidden(X11,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(esk2_3(X6,X13,X14),X14)
        | ~ r2_hidden(k4_tarski(esk2_3(X6,X13,X14),X16),X6)
        | ~ r2_hidden(X16,X13)
        | X14 = k10_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk2_3(X6,X13,X14),esk3_3(X6,X13,X14)),X6)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k10_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),X13)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k10_relat_1(X6,X13)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & ~ r1_tarski(k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k10_relat_1(esk8_0,esk6_0),k10_relat_1(esk8_0,esk7_0))) ),
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

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k10_relat_1(esk8_0,esk6_0),k10_relat_1(esk8_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30,X31] :
      ( ( r2_hidden(X27,X24)
        | ~ r2_hidden(X27,X26)
        | X26 != k3_xboole_0(X24,X25) )
      & ( r2_hidden(X27,X25)
        | ~ r2_hidden(X27,X26)
        | X26 != k3_xboole_0(X24,X25) )
      & ( ~ r2_hidden(X28,X24)
        | ~ r2_hidden(X28,X25)
        | r2_hidden(X28,X26)
        | X26 != k3_xboole_0(X24,X25) )
      & ( ~ r2_hidden(esk5_3(X29,X30,X31),X31)
        | ~ r2_hidden(esk5_3(X29,X30,X31),X29)
        | ~ r2_hidden(esk5_3(X29,X30,X31),X30)
        | X31 = k3_xboole_0(X29,X30) )
      & ( r2_hidden(esk5_3(X29,X30,X31),X29)
        | r2_hidden(esk5_3(X29,X30,X31),X31)
        | X31 = k3_xboole_0(X29,X30) )
      & ( r2_hidden(esk5_3(X29,X30,X31),X30)
        | r2_hidden(esk5_3(X29,X30,X31),X31)
        | X31 = k3_xboole_0(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,k10_relat_1(X2,X3),X1)),X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk4_2(k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k10_relat_1(esk8_0,esk6_0),k10_relat_1(esk8_0,esk7_0))),k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_4(X1,X2,k10_relat_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k10_relat_1(esk8_0,esk6_0),k10_relat_1(esk8_0,esk7_0))),esk1_4(esk8_0,k3_xboole_0(esk6_0,esk7_0),k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),esk4_2(k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k10_relat_1(esk8_0,esk6_0),k10_relat_1(esk8_0,esk7_0))))),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk1_4(esk8_0,k3_xboole_0(esk6_0,esk7_0),k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),esk4_2(k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k10_relat_1(esk8_0,esk6_0),k10_relat_1(esk8_0,esk7_0)))),k3_xboole_0(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_15]),c_0_16])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk4_2(k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k10_relat_1(esk8_0,esk6_0),k10_relat_1(esk8_0,esk7_0))),k10_relat_1(esk8_0,X1))
    | ~ r2_hidden(esk1_4(esk8_0,k3_xboole_0(esk6_0,esk7_0),k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),esk4_2(k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k10_relat_1(esk8_0,esk6_0),k10_relat_1(esk8_0,esk7_0)))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_16])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_4(esk8_0,k3_xboole_0(esk6_0,esk7_0),k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),esk4_2(k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k10_relat_1(esk8_0,esk6_0),k10_relat_1(esk8_0,esk7_0)))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(esk4_2(X1,k3_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(esk4_2(X1,k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk4_2(k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k10_relat_1(esk8_0,esk6_0),k10_relat_1(esk8_0,esk7_0))),k10_relat_1(esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_4(esk8_0,k3_xboole_0(esk6_0,esk7_0),k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),esk4_2(k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k10_relat_1(esk8_0,esk6_0),k10_relat_1(esk8_0,esk7_0)))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk4_2(k10_relat_1(esk8_0,k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k10_relat_1(esk8_0,esk6_0),k10_relat_1(esk8_0,esk7_0))),k10_relat_1(esk8_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_32]),c_0_33]),
    [proof]).

%------------------------------------------------------------------------------
