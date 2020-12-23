%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0691+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:03 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   32 (  80 expanded)
%              Number of clauses        :   21 (  36 expanded)
%              Number of leaves         :    5 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  141 ( 292 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

fof(c_0_6,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( ( ~ r1_tarski(X30,X31)
        | ~ r2_hidden(X32,X30)
        | r2_hidden(X32,X31) )
      & ( r2_hidden(esk7_2(X33,X34),X33)
        | r1_tarski(X33,X34) )
      & ( ~ r2_hidden(esk7_2(X33,X34),X34)
        | r1_tarski(X33,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & r1_tarski(esk11_0,k1_relat_1(esk12_0))
    & ~ r1_tarski(esk11_0,k10_relat_1(esk12_0,k9_relat_1(esk12_0,esk11_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X36,X37,X38,X40,X41,X42,X43,X45] :
      ( ( ~ r2_hidden(X38,X37)
        | r2_hidden(k4_tarski(X38,esk8_3(X36,X37,X38)),X36)
        | X37 != k1_relat_1(X36) )
      & ( ~ r2_hidden(k4_tarski(X40,X41),X36)
        | r2_hidden(X40,X37)
        | X37 != k1_relat_1(X36) )
      & ( ~ r2_hidden(esk9_2(X42,X43),X43)
        | ~ r2_hidden(k4_tarski(esk9_2(X42,X43),X45),X42)
        | X43 = k1_relat_1(X42) )
      & ( r2_hidden(esk9_2(X42,X43),X43)
        | r2_hidden(k4_tarski(esk9_2(X42,X43),esk10_2(X42,X43)),X42)
        | X43 = k1_relat_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(esk11_0,k1_relat_1(esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( ~ r1_tarski(esk11_0,k10_relat_1(esk12_0,k9_relat_1(esk12_0,esk11_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(esk7_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_13,plain,(
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

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,esk8_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk12_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk7_2(esk11_0,k10_relat_1(esk12_0,k9_relat_1(esk12_0,esk11_0))),esk11_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_17,plain,(
    ! [X18,X19,X20,X21,X23,X24,X25,X26,X28] :
      ( ( r2_hidden(k4_tarski(X21,esk4_4(X18,X19,X20,X21)),X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k10_relat_1(X18,X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk4_4(X18,X19,X20,X21),X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k10_relat_1(X18,X19)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X23,X24),X18)
        | ~ r2_hidden(X24,X19)
        | r2_hidden(X23,X20)
        | X20 != k10_relat_1(X18,X19)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(esk5_3(X18,X25,X26),X26)
        | ~ r2_hidden(k4_tarski(esk5_3(X18,X25,X26),X28),X18)
        | ~ r2_hidden(X28,X25)
        | X26 = k10_relat_1(X18,X25)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk5_3(X18,X25,X26),esk6_3(X18,X25,X26)),X18)
        | r2_hidden(esk5_3(X18,X25,X26),X26)
        | X26 = k10_relat_1(X18,X25)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk6_3(X18,X25,X26),X25)
        | r2_hidden(esk5_3(X18,X25,X26),X26)
        | X26 = k10_relat_1(X18,X25)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X2,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X5 != k9_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,esk8_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk7_2(esk11_0,k10_relat_1(esk12_0,k9_relat_1(esk12_0,esk11_0))),k1_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_2(esk11_0,k10_relat_1(esk12_0,k9_relat_1(esk12_0,esk11_0))),esk8_3(esk12_0,k1_relat_1(esk12_0),esk7_2(esk11_0,k10_relat_1(esk12_0,k9_relat_1(esk12_0,esk11_0))))),esk12_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk8_3(esk12_0,k1_relat_1(esk12_0),esk7_2(esk11_0,k10_relat_1(esk12_0,k9_relat_1(esk12_0,esk11_0)))),k9_relat_1(esk12_0,X1))
    | ~ r2_hidden(esk7_2(esk11_0,k10_relat_1(esk12_0,k9_relat_1(esk12_0,esk11_0))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk7_2(esk11_0,k10_relat_1(esk12_0,k9_relat_1(esk12_0,esk11_0))),k10_relat_1(esk12_0,X1))
    | ~ r2_hidden(esk8_3(esk12_0,k1_relat_1(esk12_0),esk7_2(esk11_0,k10_relat_1(esk12_0,k9_relat_1(esk12_0,esk11_0)))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_24])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk8_3(esk12_0,k1_relat_1(esk12_0),esk7_2(esk11_0,k10_relat_1(esk12_0,k9_relat_1(esk12_0,esk11_0)))),k9_relat_1(esk12_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk7_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk7_2(esk11_0,k10_relat_1(esk12_0,k9_relat_1(esk12_0,esk11_0))),k10_relat_1(esk12_0,k9_relat_1(esk12_0,esk11_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_11]),
    [proof]).

%------------------------------------------------------------------------------
