%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:41 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 999 expanded)
%              Number of clauses        :   44 ( 465 expanded)
%              Number of leaves         :    9 ( 266 expanded)
%              Depth                    :   15
%              Number of atoms          :   74 (1089 expanded)
%              Number of equality atoms :   52 ( 954 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t81_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(c_0_9,plain,(
    ! [X6] : k3_xboole_0(X6,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_10,plain,(
    ! [X11,X12] : k4_xboole_0(X11,k4_xboole_0(X11,X12)) = k3_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_11,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X7] : k4_xboole_0(X7,k1_xboole_0) = X7 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_14,plain,(
    ! [X13,X14,X15] : k3_xboole_0(X13,k4_xboole_0(X14,X15)) = k4_xboole_0(k3_xboole_0(X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_15,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_16,plain,(
    ! [X19,X20] : r1_xboole_0(k4_xboole_0(X19,X20),X20) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X8,X9,X10] : k4_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_12]),c_0_12])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_12])).

cnf(c_0_27,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_28,plain,(
    ! [X16,X17,X18] : k4_xboole_0(X16,k4_xboole_0(X17,X18)) = k2_xboole_0(k4_xboole_0(X16,X17),k3_xboole_0(X16,X18)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
       => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    inference(assume_negation,[status(cth)],[t81_xboole_1])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_25]),c_0_30]),c_0_18])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_12])).

fof(c_0_37,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ~ r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_23]),c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_38]),c_0_18]),c_0_39])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_25])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_40])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_18])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_18])).

cnf(c_0_47,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_43])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))) = X1 ),
    inference(rw,[status(thm)],[c_0_41,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),X1)) = k4_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_46])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_47])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_12])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_45,c_0_25])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,k4_xboole_0(esk1_0,X1))) = k4_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_25])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_45]),c_0_23]),c_0_18])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_45]),c_0_23])])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0))) = k4_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_25])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X2))) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_45]),c_0_25]),c_0_25])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_25])).

cnf(c_0_60,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk2_0)) = k4_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.20/0.43  # and selection function SelectNewComplexAHP.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.026 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.43  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.43  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.43  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.20/0.43  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.43  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.43  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.20/0.43  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.20/0.43  fof(t81_xboole_1, conjecture, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 0.20/0.43  fof(c_0_9, plain, ![X6]:k3_xboole_0(X6,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.43  fof(c_0_10, plain, ![X11, X12]:k4_xboole_0(X11,k4_xboole_0(X11,X12))=k3_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.43  cnf(c_0_11, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.43  cnf(c_0_12, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  fof(c_0_13, plain, ![X7]:k4_xboole_0(X7,k1_xboole_0)=X7, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.43  fof(c_0_14, plain, ![X13, X14, X15]:k3_xboole_0(X13,k4_xboole_0(X14,X15))=k4_xboole_0(k3_xboole_0(X13,X14),X15), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.20/0.43  fof(c_0_15, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.43  fof(c_0_16, plain, ![X19, X20]:r1_xboole_0(k4_xboole_0(X19,X20),X20), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.43  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.43  cnf(c_0_18, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_19, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  fof(c_0_20, plain, ![X8, X9, X10]:k4_xboole_0(k4_xboole_0(X8,X9),X10)=k4_xboole_0(X8,k2_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.20/0.43  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  cnf(c_0_22, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.43  cnf(c_0_23, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.43  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_12]), c_0_12])).
% 0.20/0.43  cnf(c_0_25, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_12])).
% 0.20/0.43  cnf(c_0_27, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.43  fof(c_0_28, plain, ![X16, X17, X18]:k4_xboole_0(X16,k4_xboole_0(X17,X18))=k2_xboole_0(k4_xboole_0(X16,X17),k3_xboole_0(X16,X18)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.20/0.43  cnf(c_0_29, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.43  cnf(c_0_30, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.43  cnf(c_0_31, plain, (k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X2))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_18])).
% 0.20/0.43  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.43  fof(c_0_33, negated_conjecture, ~(![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t81_xboole_1])).
% 0.20/0.43  cnf(c_0_34, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k4_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 0.20/0.43  cnf(c_0_35, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_25]), c_0_30]), c_0_18])).
% 0.20/0.43  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[c_0_32, c_0_12])).
% 0.20/0.43  fof(c_0_37, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))&~r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).
% 0.20/0.43  cnf(c_0_38, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.43  cnf(c_0_39, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_23]), c_0_18])).
% 0.20/0.43  cnf(c_0_40, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.43  cnf(c_0_41, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3)))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_38]), c_0_18]), c_0_39])).
% 0.20/0.43  cnf(c_0_42, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_25])).
% 0.20/0.43  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_23]), c_0_31])).
% 0.20/0.43  cnf(c_0_44, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_40])).
% 0.20/0.43  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_18])).
% 0.20/0.43  cnf(c_0_46, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_18])).
% 0.20/0.43  cnf(c_0_47, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))=k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_36, c_0_43])).
% 0.20/0.43  cnf(c_0_48, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  cnf(c_0_49, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3)))=X1), inference(rw,[status(thm)],[c_0_41, c_0_45])).
% 0.20/0.43  cnf(c_0_50, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(k4_xboole_0(esk2_0,esk3_0),X1))=k4_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_25, c_0_46])).
% 0.20/0.43  cnf(c_0_51, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_36, c_0_47])).
% 0.20/0.43  cnf(c_0_52, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_48, c_0_12])).
% 0.20/0.43  cnf(c_0_53, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=X1), inference(spm,[status(thm)],[c_0_45, c_0_25])).
% 0.20/0.43  cnf(c_0_54, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,k4_xboole_0(esk1_0,X1)))=k4_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_25])).
% 0.20/0.43  cnf(c_0_55, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_45]), c_0_23]), c_0_18])).
% 0.20/0.43  cnf(c_0_56, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_45]), c_0_23])])).
% 0.20/0.43  cnf(c_0_57, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0)))=k4_xboole_0(esk1_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_25])).
% 0.20/0.43  cnf(c_0_58, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X2)))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_45]), c_0_25]), c_0_25])).
% 0.20/0.43  cnf(c_0_59, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_56, c_0_25])).
% 0.20/0.43  cnf(c_0_60, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk2_0))=k4_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.43  cnf(c_0_61, negated_conjecture, (~r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.43  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 63
% 0.20/0.43  # Proof object clause steps            : 44
% 0.20/0.43  # Proof object formula steps           : 19
% 0.20/0.43  # Proof object conjectures             : 12
% 0.20/0.43  # Proof object clause conjectures      : 9
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 11
% 0.20/0.43  # Proof object initial formulas used   : 9
% 0.20/0.43  # Proof object generating inferences   : 23
% 0.20/0.43  # Proof object simplifying inferences  : 30
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 9
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 11
% 0.20/0.43  # Removed in clause preprocessing      : 1
% 0.20/0.43  # Initial clauses in saturation        : 10
% 0.20/0.43  # Processed clauses                    : 339
% 0.20/0.43  # ...of these trivial                  : 42
% 0.20/0.43  # ...subsumed                          : 25
% 0.20/0.43  # ...remaining for further processing  : 272
% 0.20/0.43  # Other redundant clauses eliminated   : 0
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 1
% 0.20/0.43  # Backward-rewritten                   : 55
% 0.20/0.43  # Generated clauses                    : 6806
% 0.20/0.43  # ...of the previous two non-trivial   : 2498
% 0.20/0.43  # Contextual simplify-reflections      : 0
% 0.20/0.43  # Paramodulations                      : 6802
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 4
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 206
% 0.20/0.43  #    Positive orientable unit clauses  : 196
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 1
% 0.20/0.43  #    Non-unit-clauses                  : 9
% 0.20/0.43  # Current number of unprocessed clauses: 2005
% 0.20/0.43  # ...number of literals in the above   : 2084
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 67
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 62
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 62
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 26
% 0.20/0.43  # Unit Clause-clause subsumption calls : 21
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 607
% 0.20/0.43  # BW rewrite match successes           : 46
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 70216
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.086 s
% 0.20/0.43  # System time              : 0.005 s
% 0.20/0.43  # Total time               : 0.091 s
% 0.20/0.43  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
