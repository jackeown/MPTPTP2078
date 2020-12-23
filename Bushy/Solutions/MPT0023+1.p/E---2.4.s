%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t16_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:22 EDT 2019

% Result     : Theorem 226.17s
% Output     : CNFRefutation 226.17s
% Verified   : 
% Statistics : Number of formulae       :   75 (3349 expanded)
%              Number of clauses        :   64 (1810 expanded)
%              Number of leaves         :    5 ( 769 expanded)
%              Depth                    :   17
%              Number of atoms          :  166 (16709 expanded)
%              Number of equality atoms :   49 (3698 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/xboole_1__t16_xboole_1.p',d4_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t16_xboole_1.p',d3_tarski)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t16_xboole_1.p',commutativity_k3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t16_xboole_1.p',d10_xboole_0)).

fof(t16_xboole_1,conjecture,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t16_xboole_1.p',t16_xboole_1)).

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
      & ( ~ r2_hidden(esk5_3(X25,X26,X27),X27)
        | ~ r2_hidden(esk5_3(X25,X26,X27),X25)
        | ~ r2_hidden(esk5_3(X25,X26,X27),X26)
        | X27 = k3_xboole_0(X25,X26) )
      & ( r2_hidden(esk5_3(X25,X26,X27),X25)
        | r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k3_xboole_0(X25,X26) )
      & ( r2_hidden(esk5_3(X25,X26,X27),X26)
        | r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k3_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_6,plain,(
    ! [X14,X15,X16,X17,X18] :
      ( ( ~ r1_tarski(X14,X15)
        | ~ r2_hidden(X16,X14)
        | r2_hidden(X16,X15) )
      & ( r2_hidden(esk4_2(X17,X18),X17)
        | r1_tarski(X17,X18) )
      & ( ~ r2_hidden(esk4_2(X17,X18),X18)
        | r1_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(esk4_2(X1,k3_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(esk4_2(X1,k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | r2_hidden(esk4_2(k3_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))
    | ~ r2_hidden(esk4_2(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1)),X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | r2_hidden(esk4_2(k3_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_20,plain,(
    ! [X10,X11] : k3_xboole_0(X10,X11) = k3_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_21,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = X1
    | r2_hidden(esk5_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X1))
    | ~ r2_hidden(esk4_2(X1,k3_xboole_0(X2,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_12])).

cnf(c_0_28,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_15])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk5_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))
    | ~ r2_hidden(esk4_2(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_18])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(esk5_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_25])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_18])).

cnf(c_0_36,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(X1,X2),X3),X4)
    | r2_hidden(esk4_2(k3_xboole_0(k3_xboole_0(X1,X2),X3),X4),X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_15])).

cnf(c_0_38,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),X4)
    | r2_hidden(esk4_2(k3_xboole_0(X1,k3_xboole_0(X2,X3)),X4),X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_18])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk5_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_30]),c_0_30])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3)
    | r2_hidden(esk5_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_41,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))
    | ~ r2_hidden(esk4_2(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = X1
    | ~ r2_hidden(esk5_3(X1,k3_xboole_0(X2,X3),X1),X3)
    | ~ r2_hidden(esk5_3(X1,k3_xboole_0(X2,X3),X1),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_10])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_44,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(X1,X2),X3),k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_37])).

cnf(c_0_45,plain,
    ( X1 = k3_xboole_0(X2,k3_xboole_0(X3,X4))
    | r2_hidden(esk5_3(X2,k3_xboole_0(X3,X4),X1),X1)
    | r2_hidden(esk5_3(X2,k3_xboole_0(X3,X4),X1),X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_21])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_38])).

cnf(c_0_47,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(X1,X2),X3),k3_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_37])).

cnf(c_0_49,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),X4)
    | r2_hidden(esk4_2(k3_xboole_0(X1,k3_xboole_0(X2,X3)),X4),X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_18])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk5_3(X2,k3_xboole_0(X1,X2),X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_25]),c_0_43])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,k3_xboole_0(k3_xboole_0(X2,X4),X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_44])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = X2
    | r2_hidden(esk5_3(X1,k3_xboole_0(X2,X3),X2),X2) ),
    inference(ef,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k3_xboole_0(X3,X2),X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(X1,X2),X3),k3_xboole_0(X3,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_55,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_49])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(esk5_3(X1,k3_xboole_0(X1,X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_29])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(k3_xboole_0(X2,X3),X4),X5)) = k3_xboole_0(k3_xboole_0(X2,X3),X4)
    | r2_hidden(esk5_3(X1,k3_xboole_0(k3_xboole_0(k3_xboole_0(X2,X3),X4),X5),k3_xboole_0(k3_xboole_0(X2,X3),X4)),k3_xboole_0(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_29])).

cnf(c_0_59,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X3,k3_xboole_0(X2,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_53]),c_0_54])])).

cnf(c_0_60,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))
    | ~ r2_hidden(esk4_2(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_29])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,k3_xboole_0(X3,X1))
    | ~ r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,k3_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_55])).

cnf(c_0_62,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(k3_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_63,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_49])).

fof(c_0_64,negated_conjecture,(
    ~ ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t16_xboole_1])).

cnf(c_0_65,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) = k3_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])])).

fof(c_0_66,negated_conjecture,(
    k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0) != k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_64])])])).

cnf(c_0_67,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(k3_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_65]),c_0_65])).

cnf(c_0_68,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,X3)
    | ~ r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_44])).

cnf(c_0_69,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0) != k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_70,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_67])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_43]),c_0_36])])).

cnf(c_0_72,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk3_0)) != k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_43]),c_0_70]),c_0_70]),c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])]),
    [proof]).
%------------------------------------------------------------------------------
