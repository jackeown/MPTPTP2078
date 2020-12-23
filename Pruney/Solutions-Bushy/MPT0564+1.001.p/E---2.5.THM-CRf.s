%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0564+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:49 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 310 expanded)
%              Number of clauses        :   45 ( 166 expanded)
%              Number of leaves         :    5 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  197 (1972 expanded)
%              Number of equality atoms :   50 ( 568 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

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

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t168_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(c_0_5,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( r2_hidden(X23,X20)
        | ~ r2_hidden(X23,X22)
        | X22 != k3_xboole_0(X20,X21) )
      & ( r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k3_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X20)
        | ~ r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k3_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk4_3(X25,X26,X27),X27)
        | ~ r2_hidden(esk4_3(X25,X26,X27),X25)
        | ~ r2_hidden(esk4_3(X25,X26,X27),X26)
        | X27 = k3_xboole_0(X25,X26) )
      & ( r2_hidden(esk4_3(X25,X26,X27),X25)
        | r2_hidden(esk4_3(X25,X26,X27),X27)
        | X27 = k3_xboole_0(X25,X26) )
      & ( r2_hidden(esk4_3(X25,X26,X27),X26)
        | r2_hidden(esk4_3(X25,X26,X27),X27)
        | X27 = k3_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_7,plain,(
    ! [X8,X9,X10,X11,X13,X14,X15,X16,X18] :
      ( ( r2_hidden(k4_tarski(X11,esk1_4(X8,X9,X10,X11)),X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k10_relat_1(X8,X9)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk1_4(X8,X9,X10,X11),X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k10_relat_1(X8,X9)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(k4_tarski(X13,X14),X8)
        | ~ r2_hidden(X14,X9)
        | r2_hidden(X13,X10)
        | X10 != k10_relat_1(X8,X9)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(esk2_3(X8,X15,X16),X16)
        | ~ r2_hidden(k4_tarski(esk2_3(X8,X15,X16),X18),X8)
        | ~ r2_hidden(X18,X15)
        | X16 = k10_relat_1(X8,X15)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(k4_tarski(esk2_3(X8,X15,X16),esk3_3(X8,X15,X16)),X8)
        | r2_hidden(esk2_3(X8,X15,X16),X16)
        | X16 = k10_relat_1(X8,X15)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk3_3(X8,X15,X16),X15)
        | r2_hidden(esk2_3(X8,X15,X16),X16)
        | X16 = k10_relat_1(X8,X15)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_8,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk4_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X29,X30,X31,X33] :
      ( ( r2_hidden(esk5_3(X29,X30,X31),k2_relat_1(X31))
        | ~ r2_hidden(X29,k10_relat_1(X31,X30))
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(k4_tarski(X29,esk5_3(X29,X30,X31)),X31)
        | ~ r2_hidden(X29,k10_relat_1(X31,X30))
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(esk5_3(X29,X30,X31),X30)
        | ~ r2_hidden(X29,k10_relat_1(X31,X30))
        | ~ v1_relat_1(X31) )
      & ( ~ r2_hidden(X33,k2_relat_1(X31))
        | ~ r2_hidden(k4_tarski(X29,X33),X31)
        | ~ r2_hidden(X33,X30)
        | r2_hidden(X29,k10_relat_1(X31,X30))
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk4_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,esk5_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_13,c_0_9])).

cnf(c_0_19,plain,
    ( X1 = k3_xboole_0(X2,k3_xboole_0(X3,X4))
    | r2_hidden(esk4_3(X2,k3_xboole_0(X3,X4),X1),X1)
    | r2_hidden(esk4_3(X2,k3_xboole_0(X3,X4),X1),X4) ),
    inference(spm,[status(thm)],[c_0_14,c_0_6])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(esk5_3(X1,X4,X2),X3)
    | ~ r2_hidden(X1,k10_relat_1(X2,X4))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r2_hidden(esk4_3(X2,X2,X1),X1)
    | ~ r2_hidden(esk4_3(X2,X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_18])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = X3
    | r2_hidden(esk4_3(X1,k3_xboole_0(X2,X3),X3),X3) ),
    inference(ef,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k10_relat_1(X2,k3_xboole_0(X3,X4)))
    | ~ r2_hidden(esk5_3(X1,X5,X2),X4)
    | ~ r2_hidden(esk5_3(X1,X5,X2),X3)
    | ~ r2_hidden(X1,k10_relat_1(X2,X5))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(esk5_3(X1,k3_xboole_0(X2,X3),X4),X3)
    | ~ r2_hidden(X1,k10_relat_1(X4,k3_xboole_0(X2,X3)))
    | ~ v1_relat_1(X4) ),
    inference(spm,[status(thm)],[c_0_14,c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk4_3(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),X2),k3_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_18])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k10_relat_1(X2,k3_xboole_0(X3,X4)))
    | ~ r2_hidden(esk5_3(X1,k3_xboole_0(X5,X4),X2),X3)
    | ~ r2_hidden(X1,k10_relat_1(X2,k3_xboole_0(X5,X4)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,plain,
    ( X1 = k3_xboole_0(k3_xboole_0(X2,X3),X4)
    | r2_hidden(esk4_3(k3_xboole_0(X2,X3),X4,X1),X1)
    | r2_hidden(esk4_3(k3_xboole_0(X2,X3),X4,X1),X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_27])).

fof(c_0_32,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3)
    | r2_hidden(esk4_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_9])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk4_3(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),X2),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_6]),c_0_18])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X3)))
    | ~ r2_hidden(X1,k10_relat_1(X2,k3_xboole_0(X4,X3)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = X2
    | r2_hidden(esk4_3(k3_xboole_0(X1,X2),X3,X2),X2) ),
    inference(ef,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = X3
    | ~ r2_hidden(esk4_3(k3_xboole_0(X1,X2),X3,X3),X2)
    | ~ r2_hidden(esk4_3(k3_xboole_0(X1,X2),X3,X3),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_21])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_33])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(X1,k10_relat_1(X2,k3_xboole_0(X4,X3)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_26])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk4_3(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_21]),c_0_34])).

cnf(c_0_42,plain,
    ( k3_xboole_0(k3_xboole_0(X1,k10_relat_1(X2,k3_xboole_0(X3,X4))),X5) = k10_relat_1(X2,k3_xboole_0(X3,X4))
    | r2_hidden(esk4_3(k3_xboole_0(X1,k10_relat_1(X2,k3_xboole_0(X3,X4))),X5,k10_relat_1(X2,k3_xboole_0(X3,X4))),k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X4)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_43,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    inference(assume_negation,[status(cth)],[t168_relat_1])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk4_3(k3_xboole_0(X1,X2),X2,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_9]),c_0_38]),c_0_39])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,k10_relat_1(X2,k3_xboole_0(X3,X4))) = k10_relat_1(X2,k3_xboole_0(X3,X4))
    | r2_hidden(esk4_3(X1,k10_relat_1(X2,k3_xboole_0(X3,X4)),k10_relat_1(X2,k3_xboole_0(X3,X4))),k10_relat_1(X2,X4))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_9])).

cnf(c_0_46,plain,
    ( k3_xboole_0(k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2)),k10_relat_1(X1,k3_xboole_0(X3,X2))) = k10_relat_1(X1,k3_xboole_0(X3,X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_18])])).

fof(c_0_47,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & k10_relat_1(esk7_0,esk6_0) != k10_relat_1(esk7_0,k3_xboole_0(k2_relat_1(esk7_0),esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).

cnf(c_0_48,plain,
    ( k3_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,k3_xboole_0(X3,X2))) = k10_relat_1(X1,k3_xboole_0(X3,X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_38]),c_0_39])])).

cnf(c_0_49,plain,
    ( k3_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_18]),c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( k10_relat_1(esk7_0,esk6_0) != k10_relat_1(esk7_0,k3_xboole_0(k2_relat_1(esk7_0),esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,plain,
    ( k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2)) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( k10_relat_1(esk7_0,k3_xboole_0(esk6_0,k2_relat_1(esk7_0))) != k10_relat_1(esk7_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_38])).

cnf(c_0_53,plain,
    ( k10_relat_1(X1,k3_xboole_0(X2,k2_relat_1(X1))) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])]),
    [proof]).

%------------------------------------------------------------------------------
