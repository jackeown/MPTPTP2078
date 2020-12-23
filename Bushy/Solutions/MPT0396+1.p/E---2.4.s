%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t18_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:13 EDT 2019

% Result     : Theorem 48.82s
% Output     : CNFRefutation 48.82s
% Verified   : 
% Statistics : Number of formulae       :   34 (  76 expanded)
%              Number of clauses        :   25 (  36 expanded)
%              Number of leaves         :    4 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  103 ( 276 expanded)
%              Number of equality atoms :   10 (  32 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t18_setfam_1.p',t18_setfam_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t18_setfam_1.p',d4_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t18_setfam_1.p',d3_tarski)).

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t18_setfam_1.p',d2_setfam_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_setfam_1(X1,X2)
       => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    inference(assume_negation,[status(cth)],[t18_setfam_1])).

fof(c_0_5,plain,(
    ! [X23,X24,X25,X27,X28,X29,X30,X32] :
      ( ( r2_hidden(X25,esk6_3(X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k3_tarski(X23) )
      & ( r2_hidden(esk6_3(X23,X24,X25),X23)
        | ~ r2_hidden(X25,X24)
        | X24 != k3_tarski(X23) )
      & ( ~ r2_hidden(X27,X28)
        | ~ r2_hidden(X28,X23)
        | r2_hidden(X27,X24)
        | X24 != k3_tarski(X23) )
      & ( ~ r2_hidden(esk7_2(X29,X30),X30)
        | ~ r2_hidden(esk7_2(X29,X30),X32)
        | ~ r2_hidden(X32,X29)
        | X30 = k3_tarski(X29) )
      & ( r2_hidden(esk7_2(X29,X30),esk8_2(X29,X30))
        | r2_hidden(esk7_2(X29,X30),X30)
        | X30 = k3_tarski(X29) )
      & ( r2_hidden(esk8_2(X29,X30),X29)
        | r2_hidden(esk7_2(X29,X30),X30)
        | X30 = k3_tarski(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_6,negated_conjecture,
    ( r1_setfam_1(esk1_0,esk2_0)
    & ~ r1_tarski(k3_tarski(esk1_0),k3_tarski(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ( ~ r1_tarski(X17,X18)
        | ~ r2_hidden(X19,X17)
        | r2_hidden(X19,X18) )
      & ( r2_hidden(esk5_2(X20,X21),X20)
        | r1_tarski(X20,X21) )
      & ( ~ r2_hidden(esk5_2(X20,X21),X21)
        | r1_tarski(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X13,X14,X16] :
      ( ( r2_hidden(esk3_3(X9,X10,X11),X10)
        | ~ r2_hidden(X11,X9)
        | ~ r1_setfam_1(X9,X10) )
      & ( r1_tarski(X11,esk3_3(X9,X10,X11))
        | ~ r2_hidden(X11,X9)
        | ~ r1_setfam_1(X9,X10) )
      & ( r2_hidden(esk4_2(X13,X14),X13)
        | r1_setfam_1(X13,X14) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r1_tarski(esk4_2(X13,X14),X16)
        | r1_setfam_1(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(esk1_0),k3_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X2)
    | ~ r1_setfam_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r1_setfam_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( r2_hidden(esk6_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk5_2(k3_tarski(esk1_0),k3_tarski(esk2_0)),k3_tarski(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(X1,esk3_3(esk1_0,esk2_0,X1))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,k3_tarski(esk1_0),esk5_2(k3_tarski(esk1_0),k3_tarski(esk2_0))),esk1_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,esk6_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk3_3(esk1_0,esk2_0,X1),esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_13])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk6_3(esk1_0,k3_tarski(esk1_0),esk5_2(k3_tarski(esk1_0),k3_tarski(esk2_0))),esk3_3(esk1_0,esk2_0,esk6_3(esk1_0,k3_tarski(esk1_0),esk5_2(k3_tarski(esk1_0),k3_tarski(esk2_0))))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,esk6_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk3_3(esk1_0,esk2_0,esk6_3(esk1_0,k3_tarski(esk1_0),esk5_2(k3_tarski(esk1_0),k3_tarski(esk2_0)))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,esk3_3(esk1_0,esk2_0,esk6_3(esk1_0,k3_tarski(esk1_0),esk5_2(k3_tarski(esk1_0),k3_tarski(esk2_0)))))
    | ~ r2_hidden(X1,esk6_3(esk1_0,k3_tarski(esk1_0),esk5_2(k3_tarski(esk1_0),k3_tarski(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk5_2(k3_tarski(esk1_0),k3_tarski(esk2_0)),esk6_3(esk1_0,k3_tarski(esk1_0),esk5_2(k3_tarski(esk1_0),k3_tarski(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(esk2_0))
    | ~ r2_hidden(X1,esk3_3(esk1_0,esk2_0,esk6_3(esk1_0,k3_tarski(esk1_0),esk5_2(k3_tarski(esk1_0),k3_tarski(esk2_0))))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk5_2(k3_tarski(esk1_0),k3_tarski(esk2_0)),esk3_3(esk1_0,esk2_0,esk6_3(esk1_0,k3_tarski(esk1_0),esk5_2(k3_tarski(esk1_0),k3_tarski(esk2_0))))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk5_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk5_2(k3_tarski(esk1_0),k3_tarski(esk2_0)),k3_tarski(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_10]),
    [proof]).
%------------------------------------------------------------------------------
