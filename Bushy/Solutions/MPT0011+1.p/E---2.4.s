%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t4_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:28 EDT 2019

% Result     : Theorem 6.26s
% Output     : CNFRefutation 6.26s
% Verified   : 
% Statistics : Number of formulae       :   83 (1370 expanded)
%              Number of clauses        :   65 ( 749 expanded)
%              Number of leaves         :    9 ( 316 expanded)
%              Depth                    :   16
%              Number of atoms          :  181 (6782 expanded)
%              Number of equality atoms :   48 (1517 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t4_xboole_1.p',d3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t4_xboole_1.p',d3_tarski)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t4_xboole_1.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t4_xboole_1.p',commutativity_k2_xboole_0)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t4_xboole_1.p',t7_boole)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t4_xboole_1.p',d10_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t4_xboole_1.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t4_xboole_1.p',dt_o_0_0_xboole_0)).

fof(t4_xboole_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t4_xboole_1.p',t4_xboole_1)).

fof(c_0_9,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X23,X22)
        | r2_hidden(X23,X20)
        | r2_hidden(X23,X21)
        | X22 != k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X20)
        | r2_hidden(X24,X22)
        | X22 != k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk5_3(X25,X26,X27),X25)
        | ~ r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k2_xboole_0(X25,X26) )
      & ( ~ r2_hidden(esk5_3(X25,X26,X27),X26)
        | ~ r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k2_xboole_0(X25,X26) )
      & ( r2_hidden(esk5_3(X25,X26,X27),X27)
        | r2_hidden(esk5_3(X25,X26,X27),X25)
        | r2_hidden(esk5_3(X25,X26,X27),X26)
        | X27 = k2_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_10,plain,(
    ! [X14,X15,X16,X17,X18] :
      ( ( ~ r1_tarski(X14,X15)
        | ~ r2_hidden(X16,X14)
        | r2_hidden(X16,X15) )
      & ( r2_hidden(esk4_2(X17,X18),X17)
        | r1_tarski(X17,X18) )
      & ( ~ r2_hidden(esk4_2(X17,X18),X18)
        | r1_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X3)
    | r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk4_2(X1,k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X3)
    | r2_hidden(esk4_2(k2_xboole_0(X1,X2),X3),X2)
    | r2_hidden(esk4_2(k2_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk5_3(X1,X2,X2),X1)
    | r2_hidden(esk5_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X30] : k2_xboole_0(X30,k1_xboole_0) = X30 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_26,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk4_2(X1,k2_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_19])).

cnf(c_0_28,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))
    | r2_hidden(esk4_2(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_29,plain,(
    ! [X32,X33] :
      ( ~ r2_hidden(X32,X33)
      | ~ v1_xboole_0(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
    | ~ r2_hidden(esk5_3(X3,X4,k2_xboole_0(X1,X2)),X3)
    | ~ r2_hidden(esk5_3(X3,X4,k2_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_15])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk5_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))
    | ~ r2_hidden(esk4_2(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))),X4) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

fof(c_0_37,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))
    | r2_hidden(esk4_2(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,X3)
    | ~ r2_hidden(esk5_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))
    | ~ r2_hidden(esk4_2(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_44,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X3,k2_xboole_0(X4,X1)))
    | r2_hidden(esk4_2(k2_xboole_0(X1,X2),k2_xboole_0(X3,k2_xboole_0(X4,X1))),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_21])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk5_3(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = X3
    | r2_hidden(esk5_3(k2_xboole_0(X1,X2),X3,X3),k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_31])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X3,k2_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_50,plain,(
    ! [X31] :
      ( ~ v1_xboole_0(X31)
      | X31 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))
    | ~ r2_hidden(esk4_2(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_15])).

cnf(c_0_52,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))
    | r2_hidden(esk4_2(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X1,X3)
    | ~ v1_xboole_0(X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X2,X1),X3)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_33])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))
    | ~ r2_hidden(esk4_2(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_19])).

cnf(c_0_59,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X3,X2),X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_28])).

cnf(c_0_60,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_52])).

cnf(c_0_61,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X2,X1)
    | ~ v1_xboole_0(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_62,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X2,X3),X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_28])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))
    | ~ r2_hidden(X1,k2_xboole_0(X4,X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_59])).

cnf(c_0_65,plain,
    ( r1_tarski(k2_xboole_0(k2_xboole_0(X1,X2),X3),k2_xboole_0(X3,k2_xboole_0(X2,X1)))
    | ~ v1_xboole_0(X4) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_62])).

cnf(c_0_67,plain,
    ( r1_tarski(k2_xboole_0(X1,k2_xboole_0(X2,X3)),k2_xboole_0(k2_xboole_0(X3,X2),X1))
    | ~ v1_xboole_0(X4) ),
    inference(spm,[status(thm)],[c_0_63,c_0_61])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))
    | ~ r2_hidden(esk4_2(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)),k2_xboole_0(X4,X3)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_64])).

cnf(c_0_69,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X2,X3),X4))
    | r2_hidden(esk4_2(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X2,X3),X4)),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_21])).

fof(c_0_70,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t4_xboole_1])).

cnf(c_0_71,plain,
    ( r1_tarski(k2_xboole_0(k2_xboole_0(X1,X2),X3),k2_xboole_0(X3,k2_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,plain,
    ( r1_tarski(k2_xboole_0(X1,k2_xboole_0(X2,X3)),k2_xboole_0(k2_xboole_0(X3,X2),X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_66])).

cnf(c_0_73,plain,
    ( r1_tarski(k2_xboole_0(k2_xboole_0(X1,X2),X3),k2_xboole_0(k2_xboole_0(X3,X2),X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

fof(c_0_74,negated_conjecture,(
    k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0) != k2_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_70])])])).

cnf(c_0_75,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_xboole_0(X3,X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_71]),c_0_72])])).

cnf(c_0_76,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X3,X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_73]),c_0_73])])).

cnf(c_0_77,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0) != k2_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_78,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_33])).

cnf(c_0_80,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_75,c_0_78])).

cnf(c_0_81,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    c_0_33).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(ar,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_81,c_0_78]),
    [proof]).
%------------------------------------------------------------------------------
