%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t167_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:53 EDT 2019

% Result     : Theorem 4.57s
% Output     : CNFRefutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :   24 (  45 expanded)
%              Number of clauses        :   15 (  19 expanded)
%              Number of leaves         :    4 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 161 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t167_relat_1.p',d3_tarski)).

fof(t167_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t167_relat_1.p',t167_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/relat_1__t167_relat_1.p',d14_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t167_relat_1.p',d4_relat_1)).

fof(c_0_4,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( ( ~ r1_tarski(X22,X23)
        | ~ r2_hidden(X24,X22)
        | r2_hidden(X24,X23) )
      & ( r2_hidden(esk6_2(X25,X26),X25)
        | r1_tarski(X25,X26) )
      & ( ~ r2_hidden(esk6_2(X25,X26),X26)
        | r1_tarski(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    inference(assume_negation,[status(cth)],[t167_relat_1])).

cnf(c_0_6,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,plain,(
    ! [X10,X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(k4_tarski(X13,esk3_4(X10,X11,X12,X13)),X10)
        | ~ r2_hidden(X13,X12)
        | X12 != k10_relat_1(X10,X11)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk3_4(X10,X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k10_relat_1(X10,X11)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(X15,X16),X10)
        | ~ r2_hidden(X16,X11)
        | r2_hidden(X15,X12)
        | X12 != k10_relat_1(X10,X11)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(esk4_3(X10,X17,X18),X18)
        | ~ r2_hidden(k4_tarski(esk4_3(X10,X17,X18),X20),X10)
        | ~ r2_hidden(X20,X17)
        | X18 = k10_relat_1(X10,X17)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(esk4_3(X10,X17,X18),esk5_3(X10,X17,X18)),X10)
        | r2_hidden(esk4_3(X10,X17,X18),X18)
        | X18 = k10_relat_1(X10,X17)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk5_3(X10,X17,X18),X17)
        | r2_hidden(esk4_3(X10,X17,X18),X18)
        | X18 = k10_relat_1(X10,X17)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ~ r1_tarski(k10_relat_1(esk2_0,esk1_0),k1_relat_1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_10,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

fof(c_0_11,plain,(
    ! [X28,X29,X30,X32,X33,X34,X35,X37] :
      ( ( ~ r2_hidden(X30,X29)
        | r2_hidden(k4_tarski(X30,esk7_3(X28,X29,X30)),X28)
        | X29 != k1_relat_1(X28) )
      & ( ~ r2_hidden(k4_tarski(X32,X33),X28)
        | r2_hidden(X32,X29)
        | X29 != k1_relat_1(X28) )
      & ( ~ r2_hidden(esk8_2(X34,X35),X35)
        | ~ r2_hidden(k4_tarski(esk8_2(X34,X35),X37),X34)
        | X35 = k1_relat_1(X34) )
      & ( r2_hidden(esk8_2(X34,X35),X35)
        | r2_hidden(k4_tarski(esk8_2(X34,X35),esk9_2(X34,X35)),X34)
        | X35 = k1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,esk3_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk2_0,esk1_0),k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(esk6_2(X1,X2),X3)
    | r2_hidden(esk6_2(X1,X3),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_7])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,esk3_4(X2,X3,k10_relat_1(X2,X3),X1)),X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk6_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk6_2(k10_relat_1(esk2_0,esk1_0),X1),k10_relat_1(esk2_0,esk1_0))
    | r2_hidden(esk6_2(k10_relat_1(esk2_0,esk1_0),k1_relat_1(esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X4))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk6_2(k10_relat_1(esk2_0,esk1_0),k1_relat_1(esk2_0)),k10_relat_1(esk2_0,esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk6_2(k10_relat_1(esk2_0,esk1_0),k1_relat_1(esk2_0)),X1)
    | X1 != k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_22]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
