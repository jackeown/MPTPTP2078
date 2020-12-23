%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:30 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 220 expanded)
%              Number of clauses        :   27 (  87 expanded)
%              Number of leaves         :   11 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 249 expanded)
%              Number of equality atoms :   54 ( 221 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t24_relat_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( v1_relat_1(X5)
     => ( X5 = k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))
       => ( k1_relat_1(X5) = k2_tarski(X1,X3)
          & k2_relat_1(X5) = k2_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relat_1)).

fof(fc7_relat_1,axiom,(
    ! [X1,X2,X3,X4] : v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t32_relat_1,conjecture,(
    ! [X1,X2] : k3_relat_1(k1_tarski(k4_tarski(X1,X2))) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relat_1)).

fof(c_0_11,plain,(
    ! [X21,X22] : k3_tarski(k2_tarski(X21,X22)) = k2_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X23] :
      ( ~ v1_relat_1(X23)
      | k3_relat_1(X23) = k2_xboole_0(k1_relat_1(X23),k2_relat_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X17,X18,X19,X20] : k3_enumset1(X17,X17,X18,X19,X20) = k2_enumset1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_18,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k5_xboole_0(X6,k4_xboole_0(X7,X6)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_19,plain,(
    ! [X28,X29,X30,X31,X32] :
      ( ( k1_relat_1(X32) = k2_tarski(X28,X30)
        | X32 != k2_tarski(k4_tarski(X28,X29),k4_tarski(X30,X31))
        | ~ v1_relat_1(X32) )
      & ( k2_relat_1(X32) = k2_tarski(X29,X31)
        | X32 != k2_tarski(k4_tarski(X28,X29),k4_tarski(X30,X31))
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_relat_1])])])).

fof(c_0_20,plain,(
    ! [X24,X25,X26,X27] : v1_relat_1(k2_tarski(k4_tarski(X24,X25),k4_tarski(X26,X27))) ),
    inference(variable_rename,[status(thm)],[fc7_relat_1])).

fof(c_0_21,plain,(
    ! [X8,X9,X10] : k1_enumset1(X8,X9,X10) = k2_xboole_0(k2_tarski(X8,X9),k1_tarski(X10)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_22,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_23,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k1_relat_1(X1) = k2_tarski(X2,X3)
    | X1 != k2_tarski(k4_tarski(X2,X4),k4_tarski(X3,X5))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k2_relat_1(X1) = k2_tarski(X2,X3)
    | X1 != k2_tarski(k4_tarski(X4,X2),k4_tarski(X5,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2] : k3_relat_1(k1_tarski(k4_tarski(X1,X2))) = k2_tarski(X1,X2) ),
    inference(assume_negation,[status(cth)],[t32_relat_1])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k3_relat_1(X1) = k3_tarski(k3_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_35,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_36,plain,
    ( k1_relat_1(X1) = k3_enumset1(X2,X2,X2,X2,X3)
    | X1 != k3_enumset1(k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X3,X5))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_15]),c_0_15]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_37,plain,
    ( v1_relat_1(k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_15]),c_0_25]),c_0_26])).

cnf(c_0_38,plain,
    ( k2_relat_1(X1) = k3_enumset1(X2,X2,X2,X2,X3)
    | X1 != k3_enumset1(k4_tarski(X4,X2),k4_tarski(X4,X2),k4_tarski(X4,X2),k4_tarski(X4,X2),k4_tarski(X5,X3))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_15]),c_0_15]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

fof(c_0_39,negated_conjecture,(
    k3_relat_1(k1_tarski(k4_tarski(esk1_0,esk2_0))) != k2_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_15]),c_0_15]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k1_relat_1(X1),k4_xboole_0(k2_relat_1(X1),k1_relat_1(X1))) = k3_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( k1_relat_1(k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X4))) = k3_enumset1(X1,X1,X1,X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_37])])).

cnf(c_0_43,plain,
    ( k2_relat_1(k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X4))) = k3_enumset1(X2,X2,X2,X2,X4) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_37])])).

cnf(c_0_44,negated_conjecture,
    ( k3_relat_1(k1_tarski(k4_tarski(esk1_0,esk2_0))) != k2_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k4_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X1,X1,X1,X1,X2))) = k3_enumset1(X1,X1,X1,X2,X3) ),
    inference(rw,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k4_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2))) = k3_relat_1(k3_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X4))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_37])]),c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( k3_relat_1(k3_enumset1(k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0))) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_33]),c_0_15]),c_0_15]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_48,plain,
    ( k3_relat_1(k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X2))) = k3_enumset1(X1,X1,X1,X3,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:05:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.36  #
% 0.14/0.36  # Preprocessing time       : 0.014 s
% 0.14/0.36  # Presaturation interreduction done
% 0.14/0.36  
% 0.14/0.36  # Proof found!
% 0.14/0.36  # SZS status Theorem
% 0.14/0.36  # SZS output start CNFRefutation
% 0.14/0.36  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.14/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.36  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 0.14/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.36  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.14/0.36  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.14/0.36  fof(t24_relat_1, axiom, ![X1, X2, X3, X4, X5]:(v1_relat_1(X5)=>(X5=k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))=>(k1_relat_1(X5)=k2_tarski(X1,X3)&k2_relat_1(X5)=k2_tarski(X2,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relat_1)).
% 0.14/0.36  fof(fc7_relat_1, axiom, ![X1, X2, X3, X4]:v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_relat_1)).
% 0.14/0.36  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 0.14/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.36  fof(t32_relat_1, conjecture, ![X1, X2]:k3_relat_1(k1_tarski(k4_tarski(X1,X2)))=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relat_1)).
% 0.14/0.36  fof(c_0_11, plain, ![X21, X22]:k3_tarski(k2_tarski(X21,X22))=k2_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.14/0.36  fof(c_0_12, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.36  fof(c_0_13, plain, ![X23]:(~v1_relat_1(X23)|k3_relat_1(X23)=k2_xboole_0(k1_relat_1(X23),k2_relat_1(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.14/0.36  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.36  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.36  fof(c_0_16, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.36  fof(c_0_17, plain, ![X17, X18, X19, X20]:k3_enumset1(X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.14/0.36  fof(c_0_18, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k5_xboole_0(X6,k4_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.14/0.36  fof(c_0_19, plain, ![X28, X29, X30, X31, X32]:((k1_relat_1(X32)=k2_tarski(X28,X30)|X32!=k2_tarski(k4_tarski(X28,X29),k4_tarski(X30,X31))|~v1_relat_1(X32))&(k2_relat_1(X32)=k2_tarski(X29,X31)|X32!=k2_tarski(k4_tarski(X28,X29),k4_tarski(X30,X31))|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_relat_1])])])).
% 0.14/0.36  fof(c_0_20, plain, ![X24, X25, X26, X27]:v1_relat_1(k2_tarski(k4_tarski(X24,X25),k4_tarski(X26,X27))), inference(variable_rename,[status(thm)],[fc7_relat_1])).
% 0.14/0.36  fof(c_0_21, plain, ![X8, X9, X10]:k1_enumset1(X8,X9,X10)=k2_xboole_0(k2_tarski(X8,X9),k1_tarski(X10)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.14/0.36  fof(c_0_22, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.36  cnf(c_0_23, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.36  cnf(c_0_24, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.14/0.36  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.36  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.36  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.36  cnf(c_0_28, plain, (k1_relat_1(X1)=k2_tarski(X2,X3)|X1!=k2_tarski(k4_tarski(X2,X4),k4_tarski(X3,X5))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.36  cnf(c_0_29, plain, (v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.36  cnf(c_0_30, plain, (k2_relat_1(X1)=k2_tarski(X2,X3)|X1!=k2_tarski(k4_tarski(X4,X2),k4_tarski(X5,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.36  fof(c_0_31, negated_conjecture, ~(![X1, X2]:k3_relat_1(k1_tarski(k4_tarski(X1,X2)))=k2_tarski(X1,X2)), inference(assume_negation,[status(cth)],[t32_relat_1])).
% 0.14/0.36  cnf(c_0_32, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.36  cnf(c_0_33, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.36  cnf(c_0_34, plain, (k3_relat_1(X1)=k3_tarski(k3_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])).
% 0.14/0.36  cnf(c_0_35, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_24]), c_0_25]), c_0_26])).
% 0.14/0.36  cnf(c_0_36, plain, (k1_relat_1(X1)=k3_enumset1(X2,X2,X2,X2,X3)|X1!=k3_enumset1(k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X3,X5))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_15]), c_0_15]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.14/0.36  cnf(c_0_37, plain, (v1_relat_1(k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_15]), c_0_25]), c_0_26])).
% 0.14/0.36  cnf(c_0_38, plain, (k2_relat_1(X1)=k3_enumset1(X2,X2,X2,X2,X3)|X1!=k3_enumset1(k4_tarski(X4,X2),k4_tarski(X4,X2),k4_tarski(X4,X2),k4_tarski(X4,X2),k4_tarski(X5,X3))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_15]), c_0_15]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.14/0.36  fof(c_0_39, negated_conjecture, k3_relat_1(k1_tarski(k4_tarski(esk1_0,esk2_0)))!=k2_tarski(esk1_0,esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.14/0.36  cnf(c_0_40, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_15]), c_0_15]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 0.14/0.36  cnf(c_0_41, plain, (k5_xboole_0(k1_relat_1(X1),k4_xboole_0(k2_relat_1(X1),k1_relat_1(X1)))=k3_relat_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.36  cnf(c_0_42, plain, (k1_relat_1(k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X4)))=k3_enumset1(X1,X1,X1,X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_36]), c_0_37])])).
% 0.14/0.36  cnf(c_0_43, plain, (k2_relat_1(k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X4)))=k3_enumset1(X2,X2,X2,X2,X4)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_38]), c_0_37])])).
% 0.14/0.36  cnf(c_0_44, negated_conjecture, (k3_relat_1(k1_tarski(k4_tarski(esk1_0,esk2_0)))!=k2_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.14/0.36  cnf(c_0_45, plain, (k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k4_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X1,X1,X1,X1,X2)))=k3_enumset1(X1,X1,X1,X2,X3)), inference(rw,[status(thm)],[c_0_40, c_0_35])).
% 0.14/0.36  cnf(c_0_46, plain, (k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k4_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2)))=k3_relat_1(k3_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X4)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_37])]), c_0_43])).
% 0.14/0.36  cnf(c_0_47, negated_conjecture, (k3_relat_1(k3_enumset1(k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0),k4_tarski(esk1_0,esk2_0)))!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_33]), c_0_15]), c_0_15]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.14/0.36  cnf(c_0_48, plain, (k3_relat_1(k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X2)))=k3_enumset1(X1,X1,X1,X3,X2)), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.14/0.36  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])]), ['proof']).
% 0.14/0.36  # SZS output end CNFRefutation
% 0.14/0.36  # Proof object total steps             : 50
% 0.14/0.36  # Proof object clause steps            : 27
% 0.14/0.36  # Proof object formula steps           : 23
% 0.14/0.36  # Proof object conjectures             : 6
% 0.14/0.36  # Proof object clause conjectures      : 3
% 0.14/0.36  # Proof object formula conjectures     : 3
% 0.14/0.36  # Proof object initial clauses used    : 12
% 0.14/0.36  # Proof object initial formulas used   : 11
% 0.14/0.36  # Proof object generating inferences   : 1
% 0.14/0.36  # Proof object simplifying inferences  : 58
% 0.14/0.36  # Training examples: 0 positive, 0 negative
% 0.14/0.36  # Parsed axioms                        : 11
% 0.14/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.36  # Initial clauses                      : 12
% 0.14/0.36  # Removed in clause preprocessing      : 5
% 0.14/0.36  # Initial clauses in saturation        : 7
% 0.14/0.36  # Processed clauses                    : 18
% 0.14/0.36  # ...of these trivial                  : 0
% 0.14/0.36  # ...subsumed                          : 0
% 0.14/0.36  # ...remaining for further processing  : 18
% 0.14/0.36  # Other redundant clauses eliminated   : 2
% 0.14/0.36  # Clauses deleted for lack of memory   : 0
% 0.14/0.36  # Backward-subsumed                    : 0
% 0.14/0.36  # Backward-rewritten                   : 2
% 0.14/0.36  # Generated clauses                    : 4
% 0.14/0.36  # ...of the previous two non-trivial   : 5
% 0.14/0.36  # Contextual simplify-reflections      : 0
% 0.14/0.36  # Paramodulations                      : 2
% 0.14/0.36  # Factorizations                       : 0
% 0.14/0.36  # Equation resolutions                 : 2
% 0.14/0.36  # Propositional unsat checks           : 0
% 0.14/0.36  #    Propositional check models        : 0
% 0.14/0.36  #    Propositional check unsatisfiable : 0
% 0.14/0.36  #    Propositional clauses             : 0
% 0.14/0.36  #    Propositional clauses after purity: 0
% 0.14/0.36  #    Propositional unsat core size     : 0
% 0.14/0.36  #    Propositional preprocessing time  : 0.000
% 0.14/0.36  #    Propositional encoding time       : 0.000
% 0.14/0.36  #    Propositional solver time         : 0.000
% 0.14/0.36  #    Success case prop preproc time    : 0.000
% 0.14/0.36  #    Success case prop encoding time   : 0.000
% 0.14/0.36  #    Success case prop solver time     : 0.000
% 0.14/0.36  # Current number of processed clauses  : 7
% 0.14/0.36  #    Positive orientable unit clauses  : 6
% 0.14/0.36  #    Positive unorientable unit clauses: 0
% 0.14/0.36  #    Negative unit clauses             : 0
% 0.14/0.36  #    Non-unit-clauses                  : 1
% 0.14/0.36  # Current number of unprocessed clauses: 1
% 0.14/0.36  # ...number of literals in the above   : 1
% 0.14/0.36  # Current number of archived formulas  : 0
% 0.14/0.36  # Current number of archived clauses   : 14
% 0.14/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.14/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.36  # Unit Clause-clause subsumption calls : 0
% 0.14/0.36  # Rewrite failures with RHS unbound    : 0
% 0.14/0.36  # BW rewrite match attempts            : 3
% 0.14/0.36  # BW rewrite match successes           : 2
% 0.14/0.36  # Condensation attempts                : 0
% 0.14/0.36  # Condensation successes               : 0
% 0.14/0.36  # Termbank termtop insertions          : 987
% 0.14/0.36  
% 0.14/0.36  # -------------------------------------------------
% 0.14/0.36  # User time                : 0.012 s
% 0.14/0.36  # System time              : 0.005 s
% 0.14/0.36  # Total time               : 0.017 s
% 0.14/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
