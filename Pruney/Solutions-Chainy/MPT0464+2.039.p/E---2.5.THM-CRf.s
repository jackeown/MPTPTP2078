%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:42 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 699 expanded)
%              Number of clauses        :   44 ( 295 expanded)
%              Number of leaves         :    7 ( 175 expanded)
%              Depth                    :   16
%              Number of atoms          :  168 (2140 expanded)
%              Number of equality atoms :   25 ( 327 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t48_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( r1_tarski(X1,X2)
               => r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(fc2_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & ~ r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_10,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_tarski(X14,X16)
      | r1_tarski(X14,k3_xboole_0(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_11,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))),k4_xboole_0(k5_relat_1(esk2_0,esk3_0),k4_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_12])).

fof(c_0_16,plain,(
    ! [X23,X24,X25] :
      ( ~ v1_relat_1(X23)
      | ~ v1_relat_1(X24)
      | ~ v1_relat_1(X25)
      | ~ r1_tarski(X23,X24)
      | r1_tarski(k5_relat_1(X25,X23),k5_relat_1(X25,X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))),k5_relat_1(esk2_0,esk4_0))
    | ~ r1_tarski(k5_relat_1(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))),k5_relat_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_21,plain,(
    ! [X17,X18] : r1_tarski(k4_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_22,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_relat_1(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))
    | ~ r1_tarski(k5_relat_1(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))),k5_relat_1(esk2_0,esk3_0))
    | ~ r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_relat_1(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))
    | ~ r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_18]),c_0_19]),c_0_24]),c_0_25])])).

cnf(c_0_29,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_12])).

cnf(c_0_30,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_27,c_0_12])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk4_0,X1),esk4_0)
    | r2_hidden(esk1_3(esk3_0,esk4_0,X1),X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_34,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | v1_relat_1(k4_xboole_0(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk4_0,X1),esk3_0)
    | r2_hidden(esk1_3(esk3_0,esk4_0,X1),X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_30])).

cnf(c_0_37,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X4)
    | X4 != k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_12])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X2,k4_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_32,c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,X1)),k4_xboole_0(esk4_0,X1))
    | r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,X1)),esk4_0)
    | ~ v1_relat_1(k4_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_25])).

cnf(c_0_41,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X4,k4_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_35,c_0_12])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,X1)),k4_xboole_0(esk4_0,X1))
    | r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,X1)),esk3_0)
    | ~ v1_relat_1(k4_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_25])).

cnf(c_0_44,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_12])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,X1)),k4_xboole_0(esk4_0,X1))
    | r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,X1)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_20])])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,X1)),k4_xboole_0(esk4_0,X1))
    | r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,X1)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_41]),c_0_20])])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X3,k4_xboole_0(X3,X4))
    | ~ r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X4)
    | ~ r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2)
    | ~ r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))),esk3_0)
    | r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1)) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))),esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_51])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))),esk3_0) ),
    inference(ef,[status(thm)],[c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_54])])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_55]),c_0_20])])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_56])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_55]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:30:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.71/0.92  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.71/0.92  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.71/0.92  #
% 0.71/0.92  # Preprocessing time       : 0.017 s
% 0.71/0.92  # Presaturation interreduction done
% 0.71/0.92  
% 0.71/0.92  # Proof found!
% 0.71/0.92  # SZS status Theorem
% 0.71/0.92  # SZS output start CNFRefutation
% 0.71/0.92  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 0.71/0.92  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.71/0.92  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.71/0.92  fof(t48_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 0.71/0.92  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.71/0.92  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.71/0.92  fof(fc2_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k4_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 0.71/0.92  fof(c_0_7, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 0.71/0.92  fof(c_0_8, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&~r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.71/0.92  fof(c_0_9, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.71/0.92  fof(c_0_10, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|~r1_tarski(X14,X16)|r1_tarski(X14,k3_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.71/0.92  cnf(c_0_11, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.71/0.92  cnf(c_0_12, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.71/0.92  cnf(c_0_13, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.71/0.92  cnf(c_0_14, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))),k4_xboole_0(k5_relat_1(esk2_0,esk3_0),k4_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_12])).
% 0.71/0.92  cnf(c_0_15, plain, (r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_12])).
% 0.71/0.92  fof(c_0_16, plain, ![X23, X24, X25]:(~v1_relat_1(X23)|(~v1_relat_1(X24)|(~v1_relat_1(X25)|(~r1_tarski(X23,X24)|r1_tarski(k5_relat_1(X25,X23),k5_relat_1(X25,X24)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).
% 0.71/0.92  cnf(c_0_17, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))),k5_relat_1(esk2_0,esk4_0))|~r1_tarski(k5_relat_1(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))),k5_relat_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.71/0.92  cnf(c_0_18, plain, (r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.71/0.92  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.71/0.92  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.71/0.92  fof(c_0_21, plain, ![X17, X18]:r1_tarski(k4_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.71/0.92  fof(c_0_22, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.71/0.92  cnf(c_0_23, negated_conjecture, (~v1_relat_1(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))|~r1_tarski(k5_relat_1(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))),k5_relat_1(esk2_0,esk3_0))|~r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])])).
% 0.71/0.92  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.71/0.92  cnf(c_0_25, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.71/0.92  cnf(c_0_26, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.71/0.92  cnf(c_0_27, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.71/0.92  cnf(c_0_28, negated_conjecture, (~v1_relat_1(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))|~r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_18]), c_0_19]), c_0_24]), c_0_25])])).
% 0.71/0.92  cnf(c_0_29, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_26, c_0_12])).
% 0.71/0.92  cnf(c_0_30, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_27, c_0_12])).
% 0.71/0.92  cnf(c_0_31, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.71/0.92  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.71/0.92  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk4_0,X1),esk4_0)|r2_hidden(esk1_3(esk3_0,esk4_0,X1),X1)|~v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.71/0.92  fof(c_0_34, plain, ![X21, X22]:(~v1_relat_1(X21)|v1_relat_1(k4_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).
% 0.71/0.92  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.71/0.92  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk4_0,X1),esk3_0)|r2_hidden(esk1_3(esk3_0,esk4_0,X1),X1)|~v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_30])).
% 0.71/0.92  cnf(c_0_37, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.71/0.92  cnf(c_0_38, plain, (r2_hidden(X1,X4)|X4!=k4_xboole_0(X2,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_12])).
% 0.71/0.92  cnf(c_0_39, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X2,k4_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_32, c_0_12])).
% 0.71/0.92  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,X1)),k4_xboole_0(esk4_0,X1))|r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,X1)),esk4_0)|~v1_relat_1(k4_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_33, c_0_25])).
% 0.71/0.92  cnf(c_0_41, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.71/0.92  cnf(c_0_42, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X4,k4_xboole_0(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_35, c_0_12])).
% 0.71/0.92  cnf(c_0_43, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,X1)),k4_xboole_0(esk4_0,X1))|r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,X1)),esk3_0)|~v1_relat_1(k4_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_36, c_0_25])).
% 0.71/0.92  cnf(c_0_44, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_37, c_0_12])).
% 0.71/0.92  cnf(c_0_45, plain, (r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_38])).
% 0.71/0.92  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_39])).
% 0.71/0.92  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,X1)),k4_xboole_0(esk4_0,X1))|r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,X1)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_20])])).
% 0.71/0.92  cnf(c_0_48, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(er,[status(thm)],[c_0_42])).
% 0.71/0.92  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,X1)),k4_xboole_0(esk4_0,X1))|r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,X1)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_41]), c_0_20])])).
% 0.71/0.92  cnf(c_0_50, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X3,k4_xboole_0(X3,X4))|~r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X4)|~r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3)|~r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2)|~r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.71/0.92  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))),esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.71/0.92  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))),esk3_0)|r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))),X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.71/0.92  cnf(c_0_53, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))|~r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))),esk3_0)|~r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_51])])).
% 0.71/0.92  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_3(esk3_0,esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))),esk3_0)), inference(ef,[status(thm)],[c_0_52])).
% 0.71/0.92  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_54])])).
% 0.71/0.92  cnf(c_0_56, negated_conjecture, (v1_relat_1(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_55]), c_0_20])])).
% 0.71/0.92  cnf(c_0_57, negated_conjecture, (~r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_56])])).
% 0.71/0.92  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_55]), c_0_57]), ['proof']).
% 0.71/0.92  # SZS output end CNFRefutation
% 0.71/0.92  # Proof object total steps             : 59
% 0.71/0.92  # Proof object clause steps            : 44
% 0.71/0.92  # Proof object formula steps           : 15
% 0.71/0.92  # Proof object conjectures             : 25
% 0.71/0.92  # Proof object clause conjectures      : 22
% 0.71/0.92  # Proof object formula conjectures     : 3
% 0.71/0.92  # Proof object initial clauses used    : 15
% 0.71/0.92  # Proof object initial formulas used   : 7
% 0.71/0.92  # Proof object generating inferences   : 17
% 0.71/0.92  # Proof object simplifying inferences  : 32
% 0.71/0.92  # Training examples: 0 positive, 0 negative
% 0.71/0.92  # Parsed axioms                        : 7
% 0.71/0.92  # Removed by relevancy pruning/SinE    : 0
% 0.71/0.92  # Initial clauses                      : 15
% 0.71/0.92  # Removed in clause preprocessing      : 1
% 0.71/0.92  # Initial clauses in saturation        : 14
% 0.71/0.92  # Processed clauses                    : 1173
% 0.71/0.92  # ...of these trivial                  : 10
% 0.71/0.92  # ...subsumed                          : 447
% 0.71/0.92  # ...remaining for further processing  : 715
% 0.71/0.92  # Other redundant clauses eliminated   : 3
% 0.71/0.92  # Clauses deleted for lack of memory   : 0
% 0.71/0.92  # Backward-subsumed                    : 55
% 0.71/0.92  # Backward-rewritten                   : 17
% 0.71/0.92  # Generated clauses                    : 25331
% 0.71/0.92  # ...of the previous two non-trivial   : 22932
% 0.71/0.92  # Contextual simplify-reflections      : 63
% 0.71/0.92  # Paramodulations                      : 25160
% 0.71/0.92  # Factorizations                       : 168
% 0.71/0.92  # Equation resolutions                 : 3
% 0.71/0.92  # Propositional unsat checks           : 0
% 0.71/0.92  #    Propositional check models        : 0
% 0.71/0.92  #    Propositional check unsatisfiable : 0
% 0.71/0.92  #    Propositional clauses             : 0
% 0.71/0.92  #    Propositional clauses after purity: 0
% 0.71/0.92  #    Propositional unsat core size     : 0
% 0.71/0.92  #    Propositional preprocessing time  : 0.000
% 0.71/0.92  #    Propositional encoding time       : 0.000
% 0.71/0.92  #    Propositional solver time         : 0.000
% 0.71/0.92  #    Success case prop preproc time    : 0.000
% 0.71/0.92  #    Success case prop encoding time   : 0.000
% 0.71/0.92  #    Success case prop solver time     : 0.000
% 0.71/0.92  # Current number of processed clauses  : 626
% 0.71/0.92  #    Positive orientable unit clauses  : 13
% 0.71/0.92  #    Positive unorientable unit clauses: 0
% 0.71/0.92  #    Negative unit clauses             : 3
% 0.71/0.92  #    Non-unit-clauses                  : 610
% 0.71/0.92  # Current number of unprocessed clauses: 21630
% 0.71/0.92  # ...number of literals in the above   : 133410
% 0.71/0.92  # Current number of archived formulas  : 0
% 0.71/0.92  # Current number of archived clauses   : 87
% 0.71/0.92  # Clause-clause subsumption calls (NU) : 109795
% 0.71/0.92  # Rec. Clause-clause subsumption calls : 34652
% 0.71/0.92  # Non-unit clause-clause subsumptions  : 444
% 0.71/0.92  # Unit Clause-clause subsumption calls : 1683
% 0.71/0.92  # Rewrite failures with RHS unbound    : 0
% 0.71/0.92  # BW rewrite match attempts            : 42
% 0.71/0.92  # BW rewrite match successes           : 7
% 0.71/0.92  # Condensation attempts                : 0
% 0.71/0.92  # Condensation successes               : 0
% 0.71/0.92  # Termbank termtop insertions          : 732789
% 0.71/0.93  
% 0.71/0.93  # -------------------------------------------------
% 0.71/0.93  # User time                : 0.568 s
% 0.71/0.93  # System time              : 0.022 s
% 0.71/0.93  # Total time               : 0.590 s
% 0.71/0.93  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
