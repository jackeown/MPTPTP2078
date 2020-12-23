%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:20 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   58 (  91 expanded)
%              Number of clauses        :   29 (  42 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 104 expanded)
%              Number of equality atoms :   47 (  80 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t88_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t82_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,conjecture,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(c_0_14,plain,(
    ! [X26,X27] :
      ( ~ r1_xboole_0(X26,X27)
      | k4_xboole_0(k2_xboole_0(X26,X27),X27) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).

fof(c_0_15,plain,(
    ! [X28,X29] : k2_xboole_0(X28,X29) = k5_xboole_0(X28,k4_xboole_0(X29,X28)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_16,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),X13) = k4_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_17,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,X4)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

fof(c_0_23,plain,(
    ! [X24,X25] : r1_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X25,X24)) ),
    inference(variable_rename,[status(thm)],[t82_xboole_1])).

fof(c_0_24,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_25,plain,(
    ! [X22,X23] : r1_xboole_0(k4_xboole_0(X22,X23),X23) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_26,plain,(
    ! [X8] : k3_xboole_0(X8,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_27,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t100_xboole_1])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k3_xboole_0(X14,X15)) = k4_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_33,plain,(
    ! [X18,X19,X20] : k3_xboole_0(X18,k4_xboole_0(X19,X20)) = k4_xboole_0(k3_xboole_0(X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_38,plain,(
    ! [X11] : k4_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_39,negated_conjecture,(
    k4_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_18])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_47,plain,(
    ! [X21] : k5_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_42,c_0_37])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_37]),c_0_37])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_30,c_0_44])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_48,c_0_37])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:41:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.18/0.36  # and selection function SelectNewComplexAHP.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.027 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t88_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 0.18/0.36  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.18/0.36  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.18/0.36  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.18/0.36  fof(t82_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_xboole_1)).
% 0.18/0.36  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.18/0.36  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.18/0.36  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.18/0.36  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.18/0.36  fof(t100_xboole_1, conjecture, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.18/0.36  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.18/0.36  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.18/0.36  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.18/0.36  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.18/0.36  fof(c_0_14, plain, ![X26, X27]:(~r1_xboole_0(X26,X27)|k4_xboole_0(k2_xboole_0(X26,X27),X27)=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).
% 0.18/0.36  fof(c_0_15, plain, ![X28, X29]:k2_xboole_0(X28,X29)=k5_xboole_0(X28,k4_xboole_0(X29,X28)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.18/0.36  fof(c_0_16, plain, ![X12, X13]:k4_xboole_0(k2_xboole_0(X12,X13),X13)=k4_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.18/0.36  cnf(c_0_17, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.36  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_19, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.36  fof(c_0_20, plain, ![X4, X5]:k5_xboole_0(X4,X5)=k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.18/0.36  cnf(c_0_21, plain, (k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.18/0.36  cnf(c_0_22, plain, (k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.18/0.36  fof(c_0_23, plain, ![X24, X25]:r1_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X25,X24)), inference(variable_rename,[status(thm)],[t82_xboole_1])).
% 0.18/0.36  fof(c_0_24, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.18/0.36  fof(c_0_25, plain, ![X22, X23]:r1_xboole_0(k4_xboole_0(X22,X23),X23), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.18/0.36  fof(c_0_26, plain, ![X8]:k3_xboole_0(X8,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.18/0.36  fof(c_0_27, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.18/0.36  fof(c_0_28, negated_conjecture, ~(![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t100_xboole_1])).
% 0.18/0.36  cnf(c_0_29, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.36  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.36  cnf(c_0_31, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.36  fof(c_0_32, plain, ![X14, X15]:k4_xboole_0(X14,k3_xboole_0(X14,X15))=k4_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.18/0.36  fof(c_0_33, plain, ![X18, X19, X20]:k3_xboole_0(X18,k4_xboole_0(X19,X20))=k4_xboole_0(k3_xboole_0(X18,X19),X20), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.18/0.36  cnf(c_0_34, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.36  cnf(c_0_35, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.36  cnf(c_0_36, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.36  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.36  fof(c_0_38, plain, ![X11]:k4_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.18/0.36  fof(c_0_39, negated_conjecture, k4_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.18/0.36  cnf(c_0_40, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_29, c_0_18])).
% 0.18/0.36  cnf(c_0_41, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.18/0.36  cnf(c_0_42, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.36  cnf(c_0_43, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.36  cnf(c_0_44, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.18/0.36  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.18/0.36  cnf(c_0_46, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.36  fof(c_0_47, plain, ![X21]:k5_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.18/0.36  cnf(c_0_48, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.36  cnf(c_0_49, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.36  cnf(c_0_50, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_42, c_0_37])).
% 0.18/0.36  cnf(c_0_51, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_37]), c_0_37])).
% 0.18/0.36  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_30, c_0_44])).
% 0.18/0.36  cnf(c_0_53, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.18/0.36  cnf(c_0_54, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.18/0.36  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[c_0_48, c_0_37])).
% 0.18/0.36  cnf(c_0_56, plain, (k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52]), c_0_53]), c_0_54])).
% 0.18/0.36  cnf(c_0_57, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 58
% 0.18/0.36  # Proof object clause steps            : 29
% 0.18/0.36  # Proof object formula steps           : 29
% 0.18/0.36  # Proof object conjectures             : 6
% 0.18/0.36  # Proof object clause conjectures      : 3
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 14
% 0.18/0.36  # Proof object initial formulas used   : 14
% 0.18/0.36  # Proof object generating inferences   : 4
% 0.18/0.36  # Proof object simplifying inferences  : 17
% 0.18/0.37  # Training examples: 0 positive, 0 negative
% 0.18/0.37  # Parsed axioms                        : 15
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 15
% 0.18/0.37  # Removed in clause preprocessing      : 2
% 0.18/0.37  # Initial clauses in saturation        : 13
% 0.18/0.37  # Processed clauses                    : 74
% 0.18/0.37  # ...of these trivial                  : 11
% 0.18/0.37  # ...subsumed                          : 1
% 0.18/0.37  # ...remaining for further processing  : 62
% 0.18/0.37  # Other redundant clauses eliminated   : 0
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 0
% 0.18/0.37  # Backward-rewritten                   : 3
% 0.18/0.37  # Generated clauses                    : 833
% 0.18/0.37  # ...of the previous two non-trivial   : 324
% 0.18/0.37  # Contextual simplify-reflections      : 0
% 0.18/0.37  # Paramodulations                      : 832
% 0.18/0.37  # Factorizations                       : 0
% 0.18/0.37  # Equation resolutions                 : 1
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 46
% 0.18/0.37  #    Positive orientable unit clauses  : 42
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 0
% 0.18/0.37  #    Non-unit-clauses                  : 4
% 0.18/0.37  # Current number of unprocessed clauses: 276
% 0.18/0.37  # ...number of literals in the above   : 287
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 18
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 3
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 3
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.18/0.37  # Unit Clause-clause subsumption calls : 1
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 17
% 0.18/0.37  # BW rewrite match successes           : 2
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 7205
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.035 s
% 0.18/0.37  # System time              : 0.002 s
% 0.18/0.37  # Total time               : 0.037 s
% 0.18/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
