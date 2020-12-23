%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0470+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:41 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 177 expanded)
%              Number of clauses        :   21 (  86 expanded)
%              Number of leaves         :    5 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  123 ( 616 expanded)
%              Number of equality atoms :   26 ( 110 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(c_0_5,plain,(
    ! [X7] :
      ( ~ v1_xboole_0(X7)
      | v1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_6,plain,(
    ! [X8,X9,X10,X11,X12,X14,X15,X16,X19] :
      ( ( r2_hidden(k4_tarski(X11,esk1_5(X8,X9,X10,X11,X12)),X8)
        | ~ r2_hidden(k4_tarski(X11,X12),X10)
        | X10 != k5_relat_1(X8,X9)
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(k4_tarski(esk1_5(X8,X9,X10,X11,X12),X12),X9)
        | ~ r2_hidden(k4_tarski(X11,X12),X10)
        | X10 != k5_relat_1(X8,X9)
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(k4_tarski(X14,X16),X8)
        | ~ r2_hidden(k4_tarski(X16,X15),X9)
        | r2_hidden(k4_tarski(X14,X15),X10)
        | X10 != k5_relat_1(X8,X9)
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X8,X9,X10),esk3_3(X8,X9,X10)),X10)
        | ~ r2_hidden(k4_tarski(esk2_3(X8,X9,X10),X19),X8)
        | ~ r2_hidden(k4_tarski(X19,esk3_3(X8,X9,X10)),X9)
        | X10 = k5_relat_1(X8,X9)
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(k4_tarski(esk2_3(X8,X9,X10),esk4_3(X8,X9,X10)),X8)
        | r2_hidden(k4_tarski(esk2_3(X8,X9,X10),esk3_3(X8,X9,X10)),X10)
        | X10 = k5_relat_1(X8,X9)
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(k4_tarski(esk4_3(X8,X9,X10),esk3_3(X8,X9,X10)),X9)
        | r2_hidden(k4_tarski(esk2_3(X8,X9,X10),esk3_3(X8,X9,X10)),X10)
        | X10 = k5_relat_1(X8,X9)
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

cnf(c_0_7,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk4_3(X1,X2,X3)),X1)
    | r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & ( k5_relat_1(k1_xboole_0,esk5_0) != k1_xboole_0
      | k5_relat_1(esk5_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(esk2_3(X1,X2,k1_xboole_0),esk3_3(X1,X2,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(esk2_3(X1,X2,k1_xboole_0),esk4_3(X1,X2,k1_xboole_0)),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X21,X22] :
      ( ~ r2_hidden(X21,X22)
      | ~ v1_xboole_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_16,negated_conjecture,
    ( k5_relat_1(X1,esk5_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk2_3(X1,esk5_0,k1_xboole_0),esk3_3(X1,esk5_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(esk2_3(X1,esk5_0,k1_xboole_0),esk4_3(X1,esk5_0,k1_xboole_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,esk1_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk5_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk2_3(k1_xboole_0,esk5_0,k1_xboole_0),esk4_3(k1_xboole_0,esk5_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(esk2_3(k1_xboole_0,esk5_0,k1_xboole_0),esk3_3(k1_xboole_0,esk5_0,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_11])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,esk1_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))
    | ~ v1_relat_1(k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk5_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk2_3(k1_xboole_0,esk5_0,k1_xboole_0),esk3_3(k1_xboole_0,esk5_0,k1_xboole_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_8])])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ v1_relat_1(k5_relat_1(X3,X4))
    | ~ v1_relat_1(X4)
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_20]),c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_21]),c_0_8])])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk3_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,X2),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_11]),c_0_14]),c_0_8])])).

cnf(c_0_26,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk5_0) != k1_xboole_0
    | k5_relat_1(esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(esk4_3(X1,X2,k1_xboole_0),esk3_3(X1,X2,k1_xboole_0)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_11]),c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( k5_relat_1(esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_23])])).

cnf(c_0_29,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_11]),c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_14])]),
    [proof]).

%------------------------------------------------------------------------------
