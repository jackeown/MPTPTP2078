%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t23_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:16 EDT 2019

% Result     : Theorem 163.29s
% Output     : CNFRefutation 163.29s
% Verified   : 
% Statistics : Number of formulae       :   27 (  68 expanded)
%              Number of clauses        :   20 (  30 expanded)
%              Number of leaves         :    3 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :   73 ( 258 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_setfam_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_setfam_1(X1,X2)
        & r1_setfam_1(X2,X3) )
     => r1_setfam_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',t23_setfam_1)).

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',d2_setfam_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t23_setfam_1.p',t1_xboole_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_setfam_1(X1,X2)
          & r1_setfam_1(X2,X3) )
       => r1_setfam_1(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t23_setfam_1])).

fof(c_0_4,plain,(
    ! [X10,X11,X12,X14,X15,X17] :
      ( ( r2_hidden(esk4_3(X10,X11,X12),X11)
        | ~ r2_hidden(X12,X10)
        | ~ r1_setfam_1(X10,X11) )
      & ( r1_tarski(X12,esk4_3(X10,X11,X12))
        | ~ r2_hidden(X12,X10)
        | ~ r1_setfam_1(X10,X11) )
      & ( r2_hidden(esk5_2(X14,X15),X14)
        | r1_setfam_1(X14,X15) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r1_tarski(esk5_2(X14,X15),X17)
        | r1_setfam_1(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

fof(c_0_5,negated_conjecture,
    ( r1_setfam_1(esk1_0,esk2_0)
    & r1_setfam_1(esk2_0,esk3_0)
    & ~ r1_setfam_1(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r1_setfam_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( r2_hidden(esk4_3(esk1_0,esk2_0,X1),esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_9,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,esk4_3(X2,X3,X1))
    | ~ r2_hidden(X1,X2)
    | ~ r1_setfam_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk4_3(esk1_0,esk2_0,esk5_2(esk1_0,X1)),esk2_0)
    | r1_setfam_1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_12,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ r1_tarski(X24,X25)
      | r1_tarski(X23,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk4_3(esk1_0,esk2_0,esk5_2(esk1_0,X1)),esk4_3(esk2_0,X2,esk4_3(esk1_0,esk2_0,esk5_2(esk1_0,X1))))
    | r1_setfam_1(esk1_0,X1)
    | ~ r1_setfam_1(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( r1_setfam_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk4_3(esk1_0,esk2_0,esk5_2(esk1_0,X1)),esk4_3(esk2_0,esk3_0,esk4_3(esk1_0,esk2_0,esk5_2(esk1_0,X1))))
    | r1_setfam_1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( r1_tarski(esk5_2(X1,X2),esk4_3(X1,X3,esk5_2(X1,X2)))
    | r1_setfam_1(X1,X2)
    | ~ r1_setfam_1(X1,X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(X1,esk4_3(esk2_0,esk3_0,esk4_3(esk1_0,esk2_0,esk5_2(esk1_0,X2))))
    | r1_setfam_1(esk1_0,X2)
    | ~ r1_tarski(X1,esk4_3(esk1_0,esk2_0,esk5_2(esk1_0,X2))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk5_2(esk1_0,X1),esk4_3(esk1_0,esk2_0,esk5_2(esk1_0,X1)))
    | r1_setfam_1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_7])).

cnf(c_0_20,plain,
    ( r1_setfam_1(X3,X2)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(esk5_2(X3,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk5_2(esk1_0,X1),esk4_3(esk2_0,esk3_0,esk4_3(esk1_0,esk2_0,esk5_2(esk1_0,X1))))
    | r1_setfam_1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_0,esk3_0,X1),esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_6,c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( r1_setfam_1(esk1_0,X1)
    | ~ r2_hidden(esk4_3(esk2_0,esk3_0,esk4_3(esk1_0,esk2_0,esk5_2(esk1_0,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_0,esk3_0,esk4_3(esk1_0,esk2_0,esk5_2(esk1_0,X1))),esk3_0)
    | r1_setfam_1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_setfam_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
