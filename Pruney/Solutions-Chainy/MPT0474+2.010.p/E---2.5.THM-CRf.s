%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:23 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 298 expanded)
%              Number of clauses        :   27 ( 117 expanded)
%              Number of leaves         :   17 (  90 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 337 expanded)
%              Number of equality atoms :   60 ( 295 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t41_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k6_subset_1(X1,X2)) = k6_subset_1(k4_relat_1(X1),k4_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t66_relat_1,conjecture,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(c_0_17,plain,(
    ! [X45,X46] : k1_setfam_1(k2_tarski(X45,X46)) = k3_xboole_0(X45,X46) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_18,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X41,X42] :
      ( ( k4_xboole_0(X41,k1_tarski(X42)) != X41
        | ~ r2_hidden(X42,X41) )
      & ( r2_hidden(X42,X41)
        | k4_xboole_0(X41,k1_tarski(X42)) = X41 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_23,plain,(
    ! [X13] : k2_tarski(X13,X13) = k1_tarski(X13) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_26,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X19,X20,X21,X22] : k3_enumset1(X19,X19,X20,X21,X22) = k2_enumset1(X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X23,X24,X25,X26,X27] : k4_enumset1(X23,X23,X24,X25,X26,X27) = k3_enumset1(X23,X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_29,plain,(
    ! [X28,X29,X30,X31,X32,X33] : k5_enumset1(X28,X28,X29,X30,X31,X32,X33) = k4_enumset1(X28,X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_30,plain,(
    ! [X34,X35,X36,X37,X38,X39,X40] : k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40) = k5_enumset1(X34,X35,X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_31,plain,(
    ! [X11] : k4_xboole_0(k1_xboole_0,X11) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X55,X56] :
      ( ~ v1_relat_1(X55)
      | ~ v1_relat_1(X56)
      | k4_relat_1(k6_subset_1(X55,X56)) = k6_subset_1(k4_relat_1(X55),k4_relat_1(X56)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_relat_1])])])).

fof(c_0_42,plain,(
    ! [X43,X44] : k6_subset_1(X43,X44) = k4_xboole_0(X43,X44) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_21]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

fof(c_0_45,plain,(
    ! [X47,X48,X51,X53,X54] :
      ( ( ~ v1_relat_1(X47)
        | ~ r2_hidden(X48,X47)
        | X48 = k4_tarski(esk1_2(X47,X48),esk2_2(X47,X48)) )
      & ( r2_hidden(esk3_1(X51),X51)
        | v1_relat_1(X51) )
      & ( esk3_1(X51) != k4_tarski(X53,X54)
        | v1_relat_1(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_46,plain,
    ( k4_relat_1(k6_subset_1(X1,X2)) = k6_subset_1(k4_relat_1(X1),k4_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_50,plain,(
    ! [X8] : k3_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_51,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t66_relat_1])).

cnf(c_0_52,plain,
    ( k4_relat_1(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k5_xboole_0(k4_relat_1(X1),k1_setfam_1(k6_enumset1(k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X2))))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_53,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_55,plain,(
    ! [X12] : k5_xboole_0(X12,X12) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_56,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_simplification,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k4_relat_1(X1),k1_setfam_1(k6_enumset1(k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(k1_xboole_0)))) = k4_relat_1(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_25]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_53]),c_0_58]),c_0_59]),c_0_58]),c_0_59]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.13/0.37  # and selection function SelectCQIArNpEqFirst.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.37  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.13/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.37  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.13/0.37  fof(t41_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k6_subset_1(X1,X2))=k6_subset_1(k4_relat_1(X1),k4_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_relat_1)).
% 0.13/0.37  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.13/0.37  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.13/0.37  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.13/0.37  fof(t66_relat_1, conjecture, k4_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_relat_1)).
% 0.13/0.37  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.13/0.37  fof(c_0_17, plain, ![X45, X46]:k1_setfam_1(k2_tarski(X45,X46))=k3_xboole_0(X45,X46), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.37  fof(c_0_18, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.37  fof(c_0_19, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.37  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  fof(c_0_22, plain, ![X41, X42]:((k4_xboole_0(X41,k1_tarski(X42))!=X41|~r2_hidden(X42,X41))&(r2_hidden(X42,X41)|k4_xboole_0(X41,k1_tarski(X42))=X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.13/0.37  fof(c_0_23, plain, ![X13]:k2_tarski(X13,X13)=k1_tarski(X13), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.37  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_25, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.37  fof(c_0_26, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.37  fof(c_0_27, plain, ![X19, X20, X21, X22]:k3_enumset1(X19,X19,X20,X21,X22)=k2_enumset1(X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.37  fof(c_0_28, plain, ![X23, X24, X25, X26, X27]:k4_enumset1(X23,X23,X24,X25,X26,X27)=k3_enumset1(X23,X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.37  fof(c_0_29, plain, ![X28, X29, X30, X31, X32, X33]:k5_enumset1(X28,X28,X29,X30,X31,X32,X33)=k4_enumset1(X28,X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.37  fof(c_0_30, plain, ![X34, X35, X36, X37, X38, X39, X40]:k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40)=k5_enumset1(X34,X35,X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.37  fof(c_0_31, plain, ![X11]:k4_xboole_0(k1_xboole_0,X11)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.13/0.37  cnf(c_0_32, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_33, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.37  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.37  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.37  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_38, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.37  cnf(c_0_39, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.37  cnf(c_0_40, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.37  fof(c_0_41, plain, ![X55, X56]:(~v1_relat_1(X55)|(~v1_relat_1(X56)|k4_relat_1(k6_subset_1(X55,X56))=k6_subset_1(k4_relat_1(X55),k4_relat_1(X56)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_relat_1])])])).
% 0.13/0.37  fof(c_0_42, plain, ![X43, X44]:k6_subset_1(X43,X44)=k4_xboole_0(X43,X44), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.13/0.37  cnf(c_0_43, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_21]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.13/0.37  cnf(c_0_44, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.13/0.37  fof(c_0_45, plain, ![X47, X48, X51, X53, X54]:((~v1_relat_1(X47)|(~r2_hidden(X48,X47)|X48=k4_tarski(esk1_2(X47,X48),esk2_2(X47,X48))))&((r2_hidden(esk3_1(X51),X51)|v1_relat_1(X51))&(esk3_1(X51)!=k4_tarski(X53,X54)|v1_relat_1(X51)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.13/0.37  cnf(c_0_46, plain, (k4_relat_1(k6_subset_1(X1,X2))=k6_subset_1(k4_relat_1(X1),k4_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.37  cnf(c_0_47, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.37  cnf(c_0_48, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.13/0.37  cnf(c_0_49, plain, (r2_hidden(esk3_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.37  fof(c_0_50, plain, ![X8]:k3_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.13/0.37  fof(c_0_51, negated_conjecture, ~(k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(assume_negation,[status(cth)],[t66_relat_1])).
% 0.13/0.37  cnf(c_0_52, plain, (k4_relat_1(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))=k5_xboole_0(k4_relat_1(X1),k1_setfam_1(k6_enumset1(k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X2))))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_47]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.13/0.37  cnf(c_0_53, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.37  cnf(c_0_54, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.37  fof(c_0_55, plain, ![X12]:k5_xboole_0(X12,X12)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.13/0.37  fof(c_0_56, negated_conjecture, k4_relat_1(k1_xboole_0)!=k1_xboole_0, inference(fof_simplification,[status(thm)],[c_0_51])).
% 0.13/0.37  cnf(c_0_57, plain, (k5_xboole_0(k4_relat_1(X1),k1_setfam_1(k6_enumset1(k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(X1),k4_relat_1(k1_xboole_0))))=k4_relat_1(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.37  cnf(c_0_58, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_25]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.13/0.37  cnf(c_0_59, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.13/0.37  cnf(c_0_60, negated_conjecture, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.37  cnf(c_0_61, plain, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_53]), c_0_58]), c_0_59]), c_0_58]), c_0_59]), c_0_60]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 62
% 0.13/0.37  # Proof object clause steps            : 27
% 0.13/0.37  # Proof object formula steps           : 35
% 0.13/0.37  # Proof object conjectures             : 4
% 0.13/0.37  # Proof object clause conjectures      : 1
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 17
% 0.13/0.37  # Proof object initial formulas used   : 17
% 0.13/0.37  # Proof object generating inferences   : 4
% 0.13/0.37  # Proof object simplifying inferences  : 46
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 17
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 20
% 0.13/0.37  # Removed in clause preprocessing      : 10
% 0.13/0.37  # Initial clauses in saturation        : 10
% 0.13/0.37  # Processed clauses                    : 26
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 1
% 0.13/0.37  # ...remaining for further processing  : 25
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 9
% 0.13/0.37  # ...of the previous two non-trivial   : 6
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 9
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 15
% 0.13/0.37  #    Positive orientable unit clauses  : 4
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 9
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 20
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 3
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 2
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 1
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 2
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1362
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.029 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.033 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
