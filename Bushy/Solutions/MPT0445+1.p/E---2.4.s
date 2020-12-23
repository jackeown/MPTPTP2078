%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t28_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:01 EDT 2019

% Result     : Theorem 268.09s
% Output     : CNFRefutation 268.09s
% Verified   : 
% Statistics : Number of formulae       :   36 (  66 expanded)
%              Number of clauses        :   25 (  33 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  120 ( 252 expanded)
%              Number of equality atoms :   25 (  56 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t28_relat_1.p',d5_xboole_0)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t28_relat_1.p',redefinition_k6_subset_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t28_relat_1.p',d5_relat_1)).

fof(t28_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t28_relat_1.p',t28_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t28_relat_1.p',d3_tarski)).

fof(c_0_5,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32,X33] :
      ( ( r2_hidden(X29,X26)
        | ~ r2_hidden(X29,X28)
        | X28 != k4_xboole_0(X26,X27) )
      & ( ~ r2_hidden(X29,X27)
        | ~ r2_hidden(X29,X28)
        | X28 != k4_xboole_0(X26,X27) )
      & ( ~ r2_hidden(X30,X26)
        | r2_hidden(X30,X27)
        | r2_hidden(X30,X28)
        | X28 != k4_xboole_0(X26,X27) )
      & ( ~ r2_hidden(esk7_3(X31,X32,X33),X33)
        | ~ r2_hidden(esk7_3(X31,X32,X33),X31)
        | r2_hidden(esk7_3(X31,X32,X33),X32)
        | X33 = k4_xboole_0(X31,X32) )
      & ( r2_hidden(esk7_3(X31,X32,X33),X31)
        | r2_hidden(esk7_3(X31,X32,X33),X33)
        | X33 = k4_xboole_0(X31,X32) )
      & ( ~ r2_hidden(esk7_3(X31,X32,X33),X32)
        | r2_hidden(esk7_3(X31,X32,X33),X33)
        | X33 = k4_xboole_0(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_6,plain,(
    ! [X39,X40] : k6_subset_1(X39,X40) = k4_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_7,plain,(
    ! [X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(k4_tarski(esk4_3(X15,X16,X17),X17),X15)
        | X16 != k2_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X20,X19),X15)
        | r2_hidden(X19,X16)
        | X16 != k2_relat_1(X15) )
      & ( ~ r2_hidden(esk5_2(X21,X22),X22)
        | ~ r2_hidden(k4_tarski(X24,esk5_2(X21,X22)),X21)
        | X22 = k2_relat_1(X21) )
      & ( r2_hidden(esk5_2(X21,X22),X22)
        | r2_hidden(k4_tarski(esk6_2(X21,X22),esk5_2(X21,X22)),X21)
        | X22 = k2_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X4 != k6_subset_1(X2,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k6_subset_1(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_11])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t28_relat_1])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k2_relat_1(k6_subset_1(X2,X3)))
    | r2_hidden(k4_tarski(X4,X1),X3)
    | ~ r2_hidden(k4_tarski(X4,X1),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & ~ r1_tarski(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_19,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk3_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk3_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,X2,X3),X3),X4)
    | r2_hidden(X3,k2_relat_1(k6_subset_1(X1,X4)))
    | X2 != k2_relat_1(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | X3 != k6_subset_1(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_17,c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( X3 != k6_subset_1(X4,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_9])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k2_relat_1(k6_subset_1(X2,X3)))
    | r2_hidden(X1,k2_relat_1(X3))
    | X4 != k2_relat_1(X2)
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_12,c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k6_subset_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk3_2(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0))),k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k6_subset_1(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(esk3_2(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0))),k2_relat_1(k6_subset_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k2_relat_1(k6_subset_1(X2,X3)))
    | r2_hidden(X1,k2_relat_1(X3))
    | ~ r2_hidden(X1,k2_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk3_2(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0))),k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(esk3_2(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0))),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
