%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:12 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 101 expanded)
%              Number of clauses        :   30 (  42 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 107 expanded)
%              Number of equality atoms :   65 (  97 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t22_subset_1,conjecture,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(c_0_19,plain,(
    ! [X47,X48] : k3_tarski(k2_tarski(X47,X48)) = k2_xboole_0(X47,X48) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X18,X19] : k3_xboole_0(X18,X19) = k5_xboole_0(k5_xboole_0(X18,X19),k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_22,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X22,X23,X24] : k2_enumset1(X22,X22,X23,X24) = k1_enumset1(X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X25,X26,X27,X28] : k3_enumset1(X25,X25,X26,X27,X28) = k2_enumset1(X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,plain,(
    ! [X51,X52] :
      ( ~ m1_subset_1(X52,k1_zfmisc_1(X51))
      | k3_subset_1(X51,X52) = k4_xboole_0(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_27,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X29,X30,X31,X32,X33] : k4_enumset1(X29,X29,X30,X31,X32,X33) = k3_enumset1(X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_33,plain,(
    ! [X34,X35,X36,X37,X38,X39] : k5_enumset1(X34,X34,X35,X36,X37,X38,X39) = k4_enumset1(X34,X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_34,plain,(
    ! [X40,X41,X42,X43,X44,X45,X46] : k6_enumset1(X40,X40,X41,X42,X43,X44,X45,X46) = k5_enumset1(X40,X41,X42,X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_35,plain,(
    ! [X13] : k5_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_36,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_37,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_40,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_43,plain,(
    ! [X14,X15,X16] : k5_xboole_0(k5_xboole_0(X14,X15),X16) = k5_xboole_0(X14,k5_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_44,plain,(
    ! [X17] : k5_xboole_0(X17,X17) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_47,negated_conjecture,(
    ~ ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(assume_negation,[status(cth)],[t22_subset_1])).

cnf(c_0_48,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_52,plain,(
    ! [X12] : k2_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_53,negated_conjecture,(
    k2_subset_1(esk1_0) != k3_subset_1(esk1_0,k1_subset_1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_47])])])).

fof(c_0_54,plain,(
    ! [X50] : k2_subset_1(X50) = X50 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_55,plain,(
    ! [X49] : k1_subset_1(X49) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_59,plain,(
    ! [X53] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X53)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_60,negated_conjecture,
    ( k2_subset_1(esk1_0) != k3_subset_1(esk1_0,k1_subset_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = k3_subset_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_29]),c_0_30]),c_0_31]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_65,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( esk1_0 != k3_subset_1(esk1_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_67,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_63]),c_0_64]),c_0_65])])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n009.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 15:46:41 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.11/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.11/0.35  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.11/0.35  #
% 0.11/0.35  # Preprocessing time       : 0.026 s
% 0.11/0.35  # Presaturation interreduction done
% 0.11/0.35  
% 0.11/0.35  # Proof found!
% 0.11/0.35  # SZS status Theorem
% 0.11/0.35  # SZS output start CNFRefutation
% 0.11/0.35  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.11/0.35  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.11/0.35  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.11/0.35  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.11/0.35  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.11/0.35  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.11/0.35  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.11/0.35  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.11/0.35  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.11/0.35  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.11/0.35  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.11/0.35  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.11/0.35  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.11/0.35  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.11/0.35  fof(t22_subset_1, conjecture, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 0.11/0.35  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.11/0.35  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.11/0.35  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.11/0.35  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.11/0.35  fof(c_0_19, plain, ![X47, X48]:k3_tarski(k2_tarski(X47,X48))=k2_xboole_0(X47,X48), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.11/0.35  fof(c_0_20, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.11/0.35  fof(c_0_21, plain, ![X18, X19]:k3_xboole_0(X18,X19)=k5_xboole_0(k5_xboole_0(X18,X19),k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.11/0.35  cnf(c_0_22, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.11/0.35  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.11/0.35  fof(c_0_24, plain, ![X22, X23, X24]:k2_enumset1(X22,X22,X23,X24)=k1_enumset1(X22,X23,X24), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.11/0.35  fof(c_0_25, plain, ![X25, X26, X27, X28]:k3_enumset1(X25,X25,X26,X27,X28)=k2_enumset1(X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.11/0.35  fof(c_0_26, plain, ![X51, X52]:(~m1_subset_1(X52,k1_zfmisc_1(X51))|k3_subset_1(X51,X52)=k4_xboole_0(X51,X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.11/0.35  fof(c_0_27, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.11/0.35  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.11/0.35  cnf(c_0_29, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.11/0.35  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.11/0.35  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.11/0.35  fof(c_0_32, plain, ![X29, X30, X31, X32, X33]:k4_enumset1(X29,X29,X30,X31,X32,X33)=k3_enumset1(X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.11/0.35  fof(c_0_33, plain, ![X34, X35, X36, X37, X38, X39]:k5_enumset1(X34,X34,X35,X36,X37,X38,X39)=k4_enumset1(X34,X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.11/0.35  fof(c_0_34, plain, ![X40, X41, X42, X43, X44, X45, X46]:k6_enumset1(X40,X40,X41,X42,X43,X44,X45,X46)=k5_enumset1(X40,X41,X42,X43,X44,X45,X46), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.11/0.35  fof(c_0_35, plain, ![X13]:k5_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.11/0.35  fof(c_0_36, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k5_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.11/0.35  cnf(c_0_37, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.11/0.35  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.11/0.35  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])).
% 0.11/0.35  cnf(c_0_40, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.11/0.35  cnf(c_0_41, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.11/0.35  cnf(c_0_42, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.11/0.35  fof(c_0_43, plain, ![X14, X15, X16]:k5_xboole_0(k5_xboole_0(X14,X15),X16)=k5_xboole_0(X14,k5_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.11/0.35  fof(c_0_44, plain, ![X17]:k5_xboole_0(X17,X17)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.11/0.35  cnf(c_0_45, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.11/0.35  cnf(c_0_46, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.11/0.35  fof(c_0_47, negated_conjecture, ~(![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(assume_negation,[status(cth)],[t22_subset_1])).
% 0.11/0.35  cnf(c_0_48, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.11/0.35  cnf(c_0_49, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.11/0.35  cnf(c_0_50, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.11/0.35  cnf(c_0_51, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.11/0.35  fof(c_0_52, plain, ![X12]:k2_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.11/0.35  fof(c_0_53, negated_conjecture, k2_subset_1(esk1_0)!=k3_subset_1(esk1_0,k1_subset_1(esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_47])])])).
% 0.11/0.35  fof(c_0_54, plain, ![X50]:k2_subset_1(X50)=X50, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.11/0.35  fof(c_0_55, plain, ![X49]:k1_subset_1(X49)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.11/0.35  cnf(c_0_56, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.11/0.35  cnf(c_0_57, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.11/0.35  cnf(c_0_58, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.11/0.35  fof(c_0_59, plain, ![X53]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X53)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.11/0.35  cnf(c_0_60, negated_conjecture, (k2_subset_1(esk1_0)!=k3_subset_1(esk1_0,k1_subset_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.11/0.35  cnf(c_0_61, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.11/0.35  cnf(c_0_62, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.11/0.35  cnf(c_0_63, plain, (k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))=k3_subset_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.11/0.35  cnf(c_0_64, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_29]), c_0_30]), c_0_31]), c_0_40]), c_0_41]), c_0_42])).
% 0.11/0.35  cnf(c_0_65, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.11/0.35  cnf(c_0_66, negated_conjecture, (esk1_0!=k3_subset_1(esk1_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.11/0.35  cnf(c_0_67, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_63]), c_0_64]), c_0_65])])).
% 0.11/0.35  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67])]), ['proof']).
% 0.11/0.35  # SZS output end CNFRefutation
% 0.11/0.35  # Proof object total steps             : 69
% 0.11/0.35  # Proof object clause steps            : 30
% 0.11/0.35  # Proof object formula steps           : 39
% 0.11/0.35  # Proof object conjectures             : 6
% 0.11/0.35  # Proof object clause conjectures      : 3
% 0.11/0.35  # Proof object formula conjectures     : 3
% 0.11/0.35  # Proof object initial clauses used    : 19
% 0.11/0.35  # Proof object initial formulas used   : 19
% 0.11/0.35  # Proof object generating inferences   : 3
% 0.11/0.35  # Proof object simplifying inferences  : 25
% 0.11/0.35  # Training examples: 0 positive, 0 negative
% 0.11/0.35  # Parsed axioms                        : 19
% 0.11/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.35  # Initial clauses                      : 19
% 0.11/0.35  # Removed in clause preprocessing      : 11
% 0.11/0.35  # Initial clauses in saturation        : 8
% 0.11/0.35  # Processed clauses                    : 29
% 0.11/0.35  # ...of these trivial                  : 3
% 0.11/0.35  # ...subsumed                          : 4
% 0.11/0.35  # ...remaining for further processing  : 22
% 0.11/0.35  # Other redundant clauses eliminated   : 0
% 0.11/0.35  # Clauses deleted for lack of memory   : 0
% 0.11/0.35  # Backward-subsumed                    : 0
% 0.11/0.35  # Backward-rewritten                   : 1
% 0.11/0.35  # Generated clauses                    : 92
% 0.11/0.35  # ...of the previous two non-trivial   : 50
% 0.11/0.35  # Contextual simplify-reflections      : 0
% 0.11/0.35  # Paramodulations                      : 92
% 0.11/0.35  # Factorizations                       : 0
% 0.11/0.35  # Equation resolutions                 : 0
% 0.11/0.35  # Propositional unsat checks           : 0
% 0.11/0.35  #    Propositional check models        : 0
% 0.11/0.35  #    Propositional check unsatisfiable : 0
% 0.11/0.35  #    Propositional clauses             : 0
% 0.11/0.35  #    Propositional clauses after purity: 0
% 0.11/0.35  #    Propositional unsat core size     : 0
% 0.11/0.35  #    Propositional preprocessing time  : 0.000
% 0.11/0.35  #    Propositional encoding time       : 0.000
% 0.11/0.35  #    Propositional solver time         : 0.000
% 0.11/0.35  #    Success case prop preproc time    : 0.000
% 0.11/0.35  #    Success case prop encoding time   : 0.000
% 0.11/0.35  #    Success case prop solver time     : 0.000
% 0.11/0.35  # Current number of processed clauses  : 13
% 0.11/0.35  #    Positive orientable unit clauses  : 11
% 0.11/0.35  #    Positive unorientable unit clauses: 1
% 0.11/0.35  #    Negative unit clauses             : 0
% 0.11/0.35  #    Non-unit-clauses                  : 1
% 0.11/0.35  # Current number of unprocessed clauses: 37
% 0.11/0.35  # ...number of literals in the above   : 43
% 0.11/0.35  # Current number of archived formulas  : 0
% 0.11/0.35  # Current number of archived clauses   : 20
% 0.11/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.11/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.11/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.11/0.35  # Unit Clause-clause subsumption calls : 0
% 0.11/0.35  # Rewrite failures with RHS unbound    : 0
% 0.11/0.35  # BW rewrite match attempts            : 14
% 0.11/0.35  # BW rewrite match successes           : 9
% 0.11/0.35  # Condensation attempts                : 0
% 0.11/0.35  # Condensation successes               : 0
% 0.11/0.35  # Termbank termtop insertions          : 1331
% 0.11/0.35  
% 0.11/0.35  # -------------------------------------------------
% 0.11/0.35  # User time                : 0.030 s
% 0.11/0.35  # System time              : 0.002 s
% 0.11/0.35  # Total time               : 0.032 s
% 0.11/0.35  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
