%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:26 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 146 expanded)
%              Number of clauses        :   26 (  60 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 182 expanded)
%              Number of equality atoms :   31 ( 122 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t139_zfmisc_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2,X3,X4] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
            | r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)) )
         => r1_tarski(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(t78_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(t18_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(t29_setfam_1,axiom,(
    ! [X1] : r1_setfam_1(X1,k2_setfam_1(X1,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(t90_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_enumset1)).

fof(t88_enumset1,axiom,(
    ! [X1,X2] : k4_enumset1(X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_enumset1)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(t87_enumset1,axiom,(
    ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).

fof(c_0_14,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X22,X23),k2_zfmisc_1(X24,X25))
        | r1_tarski(X23,X25)
        | v1_xboole_0(X22) )
      & ( ~ r1_tarski(k2_zfmisc_1(X23,X22),k2_zfmisc_1(X25,X24))
        | r1_tarski(X23,X25)
        | v1_xboole_0(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t139_zfmisc_1])])])])])).

fof(c_0_15,plain,(
    ! [X19,X20,X21] :
      ( ( r1_tarski(k2_zfmisc_1(X19,X21),k2_zfmisc_1(X20,X21))
        | ~ r1_tarski(X19,X20) )
      & ( r1_tarski(k2_zfmisc_1(X21,X19),k2_zfmisc_1(X21,X20))
        | ~ r1_tarski(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    inference(assume_negation,[status(cth)],[t78_relat_1])).

cnf(c_0_17,plain,
    ( r1_tarski(X2,X4)
    | v1_xboole_0(X1)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X28,X29] :
      ( ~ r1_setfam_1(X28,X29)
      | r1_tarski(k3_tarski(X28),k3_tarski(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_setfam_1])])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_21,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ r1_tarski(k1_relat_1(X32),X31)
      | k5_relat_1(k6_relat_1(X31),X32) = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X1)
    | v1_xboole_0(X2)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X30] : r1_setfam_1(X30,k2_setfam_1(X30,X30)) ),
    inference(variable_rename,[status(thm)],[t29_setfam_1])).

fof(c_0_25,plain,(
    ! [X5,X6] : k2_xboole_0(k3_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = X5 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_26,plain,(
    ! [X17,X18] : k3_tarski(k2_tarski(X17,X18)) = k2_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_27,plain,(
    ! [X26,X27] : k1_setfam_1(k2_tarski(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_28,plain,(
    ! [X7,X8] : k2_enumset1(X7,X7,X7,X8) = k2_tarski(X7,X8) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_29,plain,(
    ! [X12,X13,X14,X15] : k6_enumset1(X12,X12,X12,X12,X12,X13,X14,X15) = k2_enumset1(X12,X13,X14,X15) ),
    inference(variable_rename,[status(thm)],[t90_enumset1])).

fof(c_0_30,plain,(
    ! [X10,X11] : k4_enumset1(X10,X10,X10,X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t88_enumset1])).

cnf(c_0_31,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X1)
    | v1_xboole_0(k3_tarski(X2))
    | ~ r1_setfam_1(X2,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_35,plain,
    ( r1_setfam_1(X1,k2_setfam_1(X1,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_42,plain,(
    ! [X16] : ~ v1_xboole_0(k1_tarski(X16)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

fof(c_0_43,plain,(
    ! [X9] : k3_enumset1(X9,X9,X9,X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t87_enumset1])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk1_0),k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1)
    | v1_xboole_0(k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_46,plain,
    ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_47,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_39]),c_0_40])).

cnf(c_0_48,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( k3_tarski(k4_enumset1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47])).

cnf(c_0_52,plain,
    ( ~ v1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t139_zfmisc_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2, X3, X4]:((r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)))=>r1_tarski(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 0.20/0.38  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 0.20/0.38  fof(t78_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 0.20/0.38  fof(t18_setfam_1, axiom, ![X1, X2]:(r1_setfam_1(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_setfam_1)).
% 0.20/0.38  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 0.20/0.38  fof(t29_setfam_1, axiom, ![X1]:r1_setfam_1(X1,k2_setfam_1(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_setfam_1)).
% 0.20/0.38  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.20/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.38  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 0.20/0.38  fof(t90_enumset1, axiom, ![X1, X2, X3, X4]:k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_enumset1)).
% 0.20/0.38  fof(t88_enumset1, axiom, ![X1, X2]:k4_enumset1(X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_enumset1)).
% 0.20/0.38  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.20/0.38  fof(t87_enumset1, axiom, ![X1]:k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_enumset1)).
% 0.20/0.38  fof(c_0_14, plain, ![X22, X23, X24, X25]:((~r1_tarski(k2_zfmisc_1(X22,X23),k2_zfmisc_1(X24,X25))|r1_tarski(X23,X25)|v1_xboole_0(X22))&(~r1_tarski(k2_zfmisc_1(X23,X22),k2_zfmisc_1(X25,X24))|r1_tarski(X23,X25)|v1_xboole_0(X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t139_zfmisc_1])])])])])).
% 0.20/0.38  fof(c_0_15, plain, ![X19, X20, X21]:((r1_tarski(k2_zfmisc_1(X19,X21),k2_zfmisc_1(X20,X21))|~r1_tarski(X19,X20))&(r1_tarski(k2_zfmisc_1(X21,X19),k2_zfmisc_1(X21,X20))|~r1_tarski(X19,X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 0.20/0.38  fof(c_0_16, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1)), inference(assume_negation,[status(cth)],[t78_relat_1])).
% 0.20/0.38  cnf(c_0_17, plain, (r1_tarski(X2,X4)|v1_xboole_0(X1)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_18, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  fof(c_0_19, plain, ![X28, X29]:(~r1_setfam_1(X28,X29)|r1_tarski(k3_tarski(X28),k3_tarski(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_setfam_1])])).
% 0.20/0.38  fof(c_0_20, negated_conjecture, (v1_relat_1(esk1_0)&k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0)!=esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.38  fof(c_0_21, plain, ![X31, X32]:(~v1_relat_1(X32)|(~r1_tarski(k1_relat_1(X32),X31)|k5_relat_1(k6_relat_1(X31),X32)=X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.20/0.38  cnf(c_0_22, plain, (r1_tarski(X1,X1)|v1_xboole_0(X2)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  cnf(c_0_23, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  fof(c_0_24, plain, ![X30]:r1_setfam_1(X30,k2_setfam_1(X30,X30)), inference(variable_rename,[status(thm)],[t29_setfam_1])).
% 0.20/0.38  fof(c_0_25, plain, ![X5, X6]:k2_xboole_0(k3_xboole_0(X5,X6),k4_xboole_0(X5,X6))=X5, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.20/0.38  fof(c_0_26, plain, ![X17, X18]:k3_tarski(k2_tarski(X17,X18))=k2_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.38  fof(c_0_27, plain, ![X26, X27]:k1_setfam_1(k2_tarski(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.38  fof(c_0_28, plain, ![X7, X8]:k2_enumset1(X7,X7,X7,X8)=k2_tarski(X7,X8), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.20/0.38  fof(c_0_29, plain, ![X12, X13, X14, X15]:k6_enumset1(X12,X12,X12,X12,X12,X13,X14,X15)=k2_enumset1(X12,X13,X14,X15), inference(variable_rename,[status(thm)],[t90_enumset1])).
% 0.20/0.38  fof(c_0_30, plain, ![X10, X11]:k4_enumset1(X10,X10,X10,X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t88_enumset1])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0)!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_32, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_34, plain, (r1_tarski(X1,X1)|v1_xboole_0(k3_tarski(X2))|~r1_setfam_1(X2,X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.38  cnf(c_0_35, plain, (r1_setfam_1(X1,k2_setfam_1(X1,X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_36, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_37, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_38, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  cnf(c_0_40, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.38  cnf(c_0_41, plain, (k4_enumset1(X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.38  fof(c_0_42, plain, ![X16]:~v1_xboole_0(k1_tarski(X16)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.20/0.38  fof(c_0_43, plain, ![X9]:k3_enumset1(X9,X9,X9,X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t87_enumset1])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (~r1_tarski(k1_relat_1(esk1_0),k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.20/0.38  cnf(c_0_45, plain, (r1_tarski(X1,X1)|v1_xboole_0(k3_tarski(X2))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.38  cnf(c_0_46, plain, (k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 0.20/0.38  cnf(c_0_47, plain, (k4_enumset1(X1,X1,X1,X1,X1,X2)=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_39]), c_0_40])).
% 0.20/0.38  cnf(c_0_48, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.38  cnf(c_0_49, plain, (k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (v1_xboole_0(k3_tarski(X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.38  cnf(c_0_51, plain, (k3_tarski(k4_enumset1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47])).
% 0.20/0.38  cnf(c_0_52, plain, (~v1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1))), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.38  cnf(c_0_54, plain, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 55
% 0.20/0.38  # Proof object clause steps            : 26
% 0.20/0.38  # Proof object formula steps           : 29
% 0.20/0.38  # Proof object conjectures             : 8
% 0.20/0.38  # Proof object clause conjectures      : 5
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 15
% 0.20/0.38  # Proof object initial formulas used   : 14
% 0.20/0.38  # Proof object generating inferences   : 6
% 0.20/0.38  # Proof object simplifying inferences  : 23
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 14
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 17
% 0.20/0.38  # Removed in clause preprocessing      : 5
% 0.20/0.38  # Initial clauses in saturation        : 12
% 0.20/0.38  # Processed clauses                    : 40
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 1
% 0.20/0.38  # ...remaining for further processing  : 39
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 4
% 0.20/0.38  # Backward-rewritten                   : 12
% 0.20/0.38  # Generated clauses                    : 40
% 0.20/0.38  # ...of the previous two non-trivial   : 38
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 40
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 11
% 0.20/0.38  #    Positive orientable unit clauses  : 5
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 4
% 0.20/0.38  # Current number of unprocessed clauses: 22
% 0.20/0.38  # ...number of literals in the above   : 61
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 33
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 41
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 41
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.20/0.38  # Unit Clause-clause subsumption calls : 7
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 11
% 0.20/0.38  # BW rewrite match successes           : 11
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 1521
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.027 s
% 0.20/0.38  # System time              : 0.006 s
% 0.20/0.38  # Total time               : 0.033 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
