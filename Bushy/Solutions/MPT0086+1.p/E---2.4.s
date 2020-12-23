%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t79_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:32 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 (  55 expanded)
%              Number of clauses        :   18 (  27 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  102 ( 162 expanded)
%              Number of equality atoms :   29 (  48 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t79_xboole_1.p',d7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t79_xboole_1.p',commutativity_k3_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t79_xboole_1.p',t6_boole)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t79_xboole_1.p',d1_xboole_0)).

fof(t79_xboole_1,conjecture,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t79_xboole_1.p',t79_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t79_xboole_1.p',d4_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t79_xboole_1.p',d5_xboole_0)).

fof(c_0_7,plain,(
    ! [X33,X34] :
      ( ( ~ r1_xboole_0(X33,X34)
        | k3_xboole_0(X33,X34) = k1_xboole_0 )
      & ( k3_xboole_0(X33,X34) != k1_xboole_0
        | r1_xboole_0(X33,X34) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_8,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_9,plain,(
    ! [X41] :
      ( ~ v1_xboole_0(X41)
      | X41 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_10,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v1_xboole_0(X11)
        | ~ r2_hidden(X12,X11) )
      & ( r2_hidden(esk3_1(X13),X13)
        | v1_xboole_0(X13) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(assume_negation,[status(cth)],[t79_xboole_1])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( r2_hidden(X18,X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X15)
        | ~ r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk4_3(X20,X21,X22),X22)
        | ~ r2_hidden(esk4_3(X20,X21,X22),X20)
        | ~ r2_hidden(esk4_3(X20,X21,X22),X21)
        | X22 = k3_xboole_0(X20,X21) )
      & ( r2_hidden(esk4_3(X20,X21,X22),X20)
        | r2_hidden(esk4_3(X20,X21,X22),X22)
        | X22 = k3_xboole_0(X20,X21) )
      & ( r2_hidden(esk4_3(X20,X21,X22),X21)
        | r2_hidden(esk4_3(X20,X21,X22),X22)
        | X22 = k3_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_17,negated_conjecture,(
    ~ r1_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_20,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30,X31] :
      ( ( r2_hidden(X27,X24)
        | ~ r2_hidden(X27,X26)
        | X26 != k4_xboole_0(X24,X25) )
      & ( ~ r2_hidden(X27,X25)
        | ~ r2_hidden(X27,X26)
        | X26 != k4_xboole_0(X24,X25) )
      & ( ~ r2_hidden(X28,X24)
        | r2_hidden(X28,X25)
        | r2_hidden(X28,X26)
        | X26 != k4_xboole_0(X24,X25) )
      & ( ~ r2_hidden(esk5_3(X29,X30,X31),X31)
        | ~ r2_hidden(esk5_3(X29,X30,X31),X29)
        | r2_hidden(esk5_3(X29,X30,X31),X30)
        | X31 = k4_xboole_0(X29,X30) )
      & ( r2_hidden(esk5_3(X29,X30,X31),X29)
        | r2_hidden(esk5_3(X29,X30,X31),X31)
        | X31 = k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(esk5_3(X29,X30,X31),X30)
        | r2_hidden(esk5_3(X29,X30,X31),X31)
        | X31 = k4_xboole_0(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(esk3_1(k3_xboole_0(X1,X2)),k3_xboole_0(X1,X2))
    | r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk3_1(k3_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk2_0))),k3_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk3_1(k3_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_1(k3_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk2_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
