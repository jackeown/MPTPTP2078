%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:42 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 (5277 expanded)
%              Number of clauses        :   51 (2578 expanded)
%              Number of leaves         :    8 (1348 expanded)
%              Depth                    :   20
%              Number of atoms          :  143 (14911 expanded)
%              Number of equality atoms :   62 (6875 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t83_xboole_1,conjecture,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_8,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_10,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_11,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_12,plain,(
    ! [X20] : k3_xboole_0(X20,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X1 = k4_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk1_3(X2,X3,X1),k4_xboole_0(X4,X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_23,plain,
    ( X1 = k4_xboole_0(k4_xboole_0(X2,X3),X4)
    | r2_hidden(esk1_3(k4_xboole_0(X2,X3),X4,X1),X1)
    | ~ r2_hidden(esk1_3(k4_xboole_0(X2,X3),X4,X1),k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( X1 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3)
    | r2_hidden(esk1_3(k4_xboole_0(k1_xboole_0,X2),X3,X1),X1)
    | ~ r2_hidden(esk1_3(k4_xboole_0(k1_xboole_0,X2),X3,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1)
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_14])).

cnf(c_0_27,plain,
    ( X1 = k4_xboole_0(k1_xboole_0,X2)
    | r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_22]),c_0_14])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1) ),
    inference(ef,[status(thm)],[c_0_26])).

cnf(c_0_30,plain,
    ( X1 = k4_xboole_0(k1_xboole_0,X2)
    | ~ r2_hidden(esk1_3(k1_xboole_0,X2,X1),k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_27])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_28])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r2_hidden(esk1_3(X1,X2,k1_xboole_0),k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_29])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_27])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_35,plain,
    ( X1 = k4_xboole_0(k4_xboole_0(X2,X3),X4)
    | r2_hidden(esk1_3(k4_xboole_0(X2,X3),X4,X1),X1)
    | r2_hidden(esk1_3(k4_xboole_0(X2,X3),X4,X1),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_14])).

fof(c_0_36,plain,(
    ! [X16,X17] :
      ( ( ~ r1_xboole_0(X16,X17)
        | k3_xboole_0(X16,X17) = k1_xboole_0 )
      & ( k3_xboole_0(X16,X17) != k1_xboole_0
        | r1_xboole_0(X16,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k1_xboole_0
    | r2_hidden(esk1_3(k4_xboole_0(X1,X2),X3,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_40,plain,(
    ! [X25,X26] : r1_xboole_0(k4_xboole_0(X25,X26),X26) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_41,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_xboole_0(X1,X2)
      <=> k4_xboole_0(X1,X2) = X1 ) ),
    inference(assume_negation,[status(cth)],[t83_xboole_1])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_34])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_16])).

cnf(c_0_44,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_45,plain,(
    ! [X18,X19] :
      ( ~ r1_xboole_0(X18,X19)
      | r1_xboole_0(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_46,negated_conjecture,
    ( ( ~ r1_xboole_0(esk2_0,esk3_0)
      | k4_xboole_0(esk2_0,esk3_0) != esk2_0 )
    & ( r1_xboole_0(esk2_0,esk3_0)
      | k4_xboole_0(esk2_0,esk3_0) = esk2_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_20])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_42])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_20])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0)
    | k4_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X1)),k1_xboole_0) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = esk2_0
    | r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,X2)),k4_xboole_0(X2,k1_xboole_0)),k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_13])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_14])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)) = k1_xboole_0
    | k4_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_55]),c_0_20])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_33]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k1_xboole_0) = k4_xboole_0(esk2_0,k1_xboole_0)
    | k4_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_59])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk3_0)
    | k4_xboole_0(esk2_0,esk3_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_63])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65])])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_65]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.20/0.50  # and selection function SelectCQIArNpEqFirst.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.026 s
% 0.20/0.50  # Presaturation interreduction done
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.50  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.50  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.50  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.50  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.50  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.50  fof(t83_xboole_1, conjecture, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.50  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.50  fof(c_0_8, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.50  cnf(c_0_9, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.50  fof(c_0_10, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.50  fof(c_0_11, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.50  fof(c_0_12, plain, ![X20]:k3_xboole_0(X20,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.50  cnf(c_0_13, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_9])).
% 0.20/0.50  cnf(c_0_14, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.50  cnf(c_0_15, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.50  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.50  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.50  cnf(c_0_18, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.50  cnf(c_0_19, plain, (X1=k4_xboole_0(X2,X3)|r2_hidden(esk1_3(X2,X3,X1),X1)|~r2_hidden(esk1_3(X2,X3,X1),k4_xboole_0(X4,X2))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.50  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_16])).
% 0.20/0.50  cnf(c_0_21, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_17])).
% 0.20/0.50  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_18, c_0_16])).
% 0.20/0.50  cnf(c_0_23, plain, (X1=k4_xboole_0(k4_xboole_0(X2,X3),X4)|r2_hidden(esk1_3(k4_xboole_0(X2,X3),X4,X1),X1)|~r2_hidden(esk1_3(k4_xboole_0(X2,X3),X4,X1),k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.50  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.50  cnf(c_0_25, plain, (X1=k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3)|r2_hidden(esk1_3(k4_xboole_0(k1_xboole_0,X2),X3,X1),X1)|~r2_hidden(esk1_3(k4_xboole_0(k1_xboole_0,X2),X3,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.20/0.50  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1)|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_24, c_0_14])).
% 0.20/0.50  cnf(c_0_27, plain, (X1=k4_xboole_0(k1_xboole_0,X2)|r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_22]), c_0_14])).
% 0.20/0.50  cnf(c_0_28, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_20])).
% 0.20/0.50  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1)), inference(ef,[status(thm)],[c_0_26])).
% 0.20/0.50  cnf(c_0_30, plain, (X1=k4_xboole_0(k1_xboole_0,X2)|~r2_hidden(esk1_3(k1_xboole_0,X2,X1),k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_13, c_0_27])).
% 0.20/0.50  cnf(c_0_31, plain, (k4_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_28])).
% 0.20/0.50  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r2_hidden(esk1_3(X1,X2,k1_xboole_0),k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_13, c_0_29])).
% 0.20/0.50  cnf(c_0_33, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_27])).
% 0.20/0.50  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.50  cnf(c_0_35, plain, (X1=k4_xboole_0(k4_xboole_0(X2,X3),X4)|r2_hidden(esk1_3(k4_xboole_0(X2,X3),X4,X1),X1)|r2_hidden(esk1_3(k4_xboole_0(X2,X3),X4,X1),X2)), inference(spm,[status(thm)],[c_0_21, c_0_14])).
% 0.20/0.50  fof(c_0_36, plain, ![X16, X17]:((~r1_xboole_0(X16,X17)|k3_xboole_0(X16,X17)=k1_xboole_0)&(k3_xboole_0(X16,X17)!=k1_xboole_0|r1_xboole_0(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.50  cnf(c_0_37, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.50  cnf(c_0_38, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k1_xboole_0|r2_hidden(esk1_3(k4_xboole_0(X1,X2),X3,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.50  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.50  fof(c_0_40, plain, ![X25, X26]:r1_xboole_0(k4_xboole_0(X25,X26),X26), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.50  fof(c_0_41, negated_conjecture, ~(![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1)), inference(assume_negation,[status(cth)],[t83_xboole_1])).
% 0.20/0.50  cnf(c_0_42, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_34])).
% 0.20/0.50  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_16])).
% 0.20/0.50  cnf(c_0_44, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.50  fof(c_0_45, plain, ![X18, X19]:(~r1_xboole_0(X18,X19)|r1_xboole_0(X19,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.50  fof(c_0_46, negated_conjecture, ((~r1_xboole_0(esk2_0,esk3_0)|k4_xboole_0(esk2_0,esk3_0)!=esk2_0)&(r1_xboole_0(esk2_0,esk3_0)|k4_xboole_0(esk2_0,esk3_0)=esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).
% 0.20/0.50  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 0.20/0.50  cnf(c_0_48, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_20])).
% 0.20/0.50  cnf(c_0_49, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_20, c_0_42])).
% 0.20/0.50  cnf(c_0_50, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_20])).
% 0.20/0.50  cnf(c_0_51, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.50  cnf(c_0_52, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)|k4_xboole_0(esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.50  cnf(c_0_53, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k1_xboole_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.50  cnf(c_0_54, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X1)),k1_xboole_0)=k4_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.50  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=esk2_0|r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.50  cnf(c_0_56, plain, (~r2_hidden(X1,k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,X2)),k4_xboole_0(X2,k1_xboole_0)),k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_13])).
% 0.20/0.50  cnf(c_0_57, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.50  cnf(c_0_58, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_14])).
% 0.20/0.50  cnf(c_0_59, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))=k1_xboole_0|k4_xboole_0(esk2_0,esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_55]), c_0_20])).
% 0.20/0.50  cnf(c_0_60, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_33]), c_0_33]), c_0_33]), c_0_33])).
% 0.20/0.50  cnf(c_0_61, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_58])).
% 0.20/0.50  cnf(c_0_62, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k1_xboole_0)=k4_xboole_0(esk2_0,k1_xboole_0)|k4_xboole_0(esk2_0,esk3_0)=esk2_0), inference(spm,[status(thm)],[c_0_49, c_0_59])).
% 0.20/0.50  cnf(c_0_63, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.50  cnf(c_0_64, negated_conjecture, (~r1_xboole_0(esk2_0,esk3_0)|k4_xboole_0(esk2_0,esk3_0)!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.50  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_63])])).
% 0.20/0.50  cnf(c_0_66, negated_conjecture, (~r1_xboole_0(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65])])).
% 0.20/0.50  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_65]), c_0_66]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 68
% 0.20/0.50  # Proof object clause steps            : 51
% 0.20/0.50  # Proof object formula steps           : 17
% 0.20/0.50  # Proof object conjectures             : 11
% 0.20/0.50  # Proof object clause conjectures      : 8
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 13
% 0.20/0.50  # Proof object initial formulas used   : 8
% 0.20/0.50  # Proof object generating inferences   : 31
% 0.20/0.50  # Proof object simplifying inferences  : 22
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 9
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 16
% 0.20/0.50  # Removed in clause preprocessing      : 1
% 0.20/0.50  # Initial clauses in saturation        : 15
% 0.20/0.50  # Processed clauses                    : 1202
% 0.20/0.50  # ...of these trivial                  : 49
% 0.20/0.50  # ...subsumed                          : 800
% 0.20/0.50  # ...remaining for further processing  : 352
% 0.20/0.50  # Other redundant clauses eliminated   : 13
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 25
% 0.20/0.50  # Backward-rewritten                   : 225
% 0.20/0.50  # Generated clauses                    : 7645
% 0.20/0.50  # ...of the previous two non-trivial   : 4907
% 0.20/0.50  # Contextual simplify-reflections      : 6
% 0.20/0.50  # Paramodulations                      : 7612
% 0.20/0.50  # Factorizations                       : 20
% 0.20/0.50  # Equation resolutions                 : 13
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 84
% 0.20/0.50  #    Positive orientable unit clauses  : 19
% 0.20/0.50  #    Positive unorientable unit clauses: 1
% 0.20/0.50  #    Negative unit clauses             : 2
% 0.20/0.50  #    Non-unit-clauses                  : 62
% 0.20/0.50  # Current number of unprocessed clauses: 3683
% 0.20/0.50  # ...number of literals in the above   : 10284
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 266
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 9333
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 8016
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 763
% 0.20/0.50  # Unit Clause-clause subsumption calls : 504
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 209
% 0.20/0.50  # BW rewrite match successes           : 56
% 0.20/0.50  # Condensation attempts                : 0
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 139282
% 0.20/0.50  
% 0.20/0.50  # -------------------------------------------------
% 0.20/0.50  # User time                : 0.152 s
% 0.20/0.50  # System time              : 0.008 s
% 0.20/0.50  # Total time               : 0.160 s
% 0.20/0.50  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
