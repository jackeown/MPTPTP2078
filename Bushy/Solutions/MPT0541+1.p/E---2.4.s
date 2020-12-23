%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t143_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:50 EDT 2019

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   24 (  70 expanded)
%              Number of clauses        :   17 (  28 expanded)
%              Number of leaves         :    3 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 456 expanded)
%              Number of equality atoms :   22 (  53 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t143_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t143_relat_1.p',t143_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/relat_1__t143_relat_1.p',d13_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t143_relat_1.p',d4_relat_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(X1,k9_relat_1(X3,X2))
        <=> ? [X4] :
              ( r2_hidden(X4,k1_relat_1(X3))
              & r2_hidden(k4_tarski(X4,X1),X3)
              & r2_hidden(X4,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t143_relat_1])).

fof(c_0_4,plain,(
    ! [X13,X14,X15,X16,X18,X19,X20,X21,X23] :
      ( ( r2_hidden(k4_tarski(esk5_4(X13,X14,X15,X16),X16),X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k9_relat_1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk5_4(X13,X14,X15,X16),X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k9_relat_1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X19,X18),X13)
        | ~ r2_hidden(X19,X14)
        | r2_hidden(X18,X15)
        | X15 != k9_relat_1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(esk6_3(X13,X20,X21),X21)
        | ~ r2_hidden(k4_tarski(X23,esk6_3(X13,X20,X21)),X13)
        | ~ r2_hidden(X23,X20)
        | X21 = k9_relat_1(X13,X20)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk7_3(X13,X20,X21),esk6_3(X13,X20,X21)),X13)
        | r2_hidden(esk6_3(X13,X20,X21),X21)
        | X21 = k9_relat_1(X13,X20)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk7_3(X13,X20,X21),X20)
        | r2_hidden(esk6_3(X13,X20,X21),X21)
        | X21 = k9_relat_1(X13,X20)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X9] :
      ( v1_relat_1(esk3_0)
      & ( ~ r2_hidden(esk1_0,k9_relat_1(esk3_0,esk2_0))
        | ~ r2_hidden(X9,k1_relat_1(esk3_0))
        | ~ r2_hidden(k4_tarski(X9,esk1_0),esk3_0)
        | ~ r2_hidden(X9,esk2_0) )
      & ( r2_hidden(esk4_0,k1_relat_1(esk3_0))
        | r2_hidden(esk1_0,k9_relat_1(esk3_0,esk2_0)) )
      & ( r2_hidden(k4_tarski(esk4_0,esk1_0),esk3_0)
        | r2_hidden(esk1_0,k9_relat_1(esk3_0,esk2_0)) )
      & ( r2_hidden(esk4_0,esk2_0)
        | r2_hidden(esk1_0,k9_relat_1(esk3_0,esk2_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(X2,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X5 != k9_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,esk1_0),esk3_0)
    | r2_hidden(esk1_0,k9_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk1_0,k9_relat_1(esk3_0,esk2_0))
    | r2_hidden(esk1_0,X1)
    | X1 != k9_relat_1(esk3_0,X2)
    | ~ r2_hidden(esk4_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk1_0,k9_relat_1(esk3_0,esk2_0))
    | r2_hidden(esk1_0,k9_relat_1(esk3_0,X1))
    | ~ r2_hidden(esk4_0,X1) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0)
    | r2_hidden(esk1_0,k9_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k9_relat_1(esk3_0,esk2_0))
    | ~ r2_hidden(X1,k1_relat_1(esk3_0))
    | ~ r2_hidden(k4_tarski(X1,esk1_0),esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk1_0,k9_relat_1(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_14,plain,(
    ! [X25,X26,X27,X29,X30,X31,X32,X34] :
      ( ( ~ r2_hidden(X27,X26)
        | r2_hidden(k4_tarski(X27,esk8_3(X25,X26,X27)),X25)
        | X26 != k1_relat_1(X25) )
      & ( ~ r2_hidden(k4_tarski(X29,X30),X25)
        | r2_hidden(X29,X26)
        | X26 != k1_relat_1(X25) )
      & ( ~ r2_hidden(esk9_2(X31,X32),X32)
        | ~ r2_hidden(k4_tarski(esk9_2(X31,X32),X34),X31)
        | X32 = k1_relat_1(X31) )
      & ( r2_hidden(esk9_2(X31,X32),X32)
        | r2_hidden(k4_tarski(esk9_2(X31,X32),esk10_2(X31,X32)),X31)
        | X32 = k1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_15,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk1_0),esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk3_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13])])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(esk5_4(X1,X2,X3,X4),X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( X1 != k9_relat_1(esk3_0,X2)
    | ~ r2_hidden(esk5_4(esk3_0,X2,X1,esk1_0),k1_relat_1(esk3_0))
    | ~ r2_hidden(esk5_4(esk3_0,X2,X1,esk1_0),esk2_0)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_8])])).

cnf(c_0_19,plain,
    ( r2_hidden(esk5_4(X1,X2,X3,X4),X5)
    | X3 != k9_relat_1(X1,X2)
    | X5 != k1_relat_1(X1)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( X1 != k9_relat_1(esk3_0,X2)
    | ~ r2_hidden(esk5_4(esk3_0,X2,X1,esk1_0),esk2_0)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_8])])).

cnf(c_0_21,plain,
    ( r2_hidden(esk5_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_22,negated_conjecture,
    ( X1 != k9_relat_1(esk3_0,esk2_0)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_8])])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_22,c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
