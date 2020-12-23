%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:13 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 128 expanded)
%              Number of clauses        :   22 (  49 expanded)
%              Number of leaves         :   11 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   72 ( 191 expanded)
%              Number of equality atoms :   39 ( 121 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

fof(t38_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
       => k1_funct_1(X3,X1) = k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).

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

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(c_0_11,plain,(
    ! [X37,X38] : k1_setfam_1(k2_tarski(X37,X38)) = k3_xboole_0(X37,X38) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_12,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
         => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t71_funct_1])).

fof(c_0_14,plain,(
    ! [X41,X42,X43] :
      ( ~ v1_relat_1(X43)
      | ~ v1_funct_1(X43)
      | ~ r2_hidden(X41,k3_xboole_0(k1_relat_1(X43),X42))
      | k1_funct_1(X43,X41) = k1_funct_1(k5_relat_1(k6_relat_1(X42),X43),X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_funct_1])])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X15,X16,X17,X18] : k3_enumset1(X15,X15,X16,X17,X18) = k2_enumset1(X15,X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_19,plain,(
    ! [X19,X20,X21,X22,X23] : k4_enumset1(X19,X19,X20,X21,X22,X23) = k3_enumset1(X19,X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_20,plain,(
    ! [X24,X25,X26,X27,X28,X29] : k5_enumset1(X24,X24,X25,X26,X27,X28,X29) = k4_enumset1(X24,X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_21,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36] : k6_enumset1(X30,X30,X31,X32,X33,X34,X35,X36) = k5_enumset1(X30,X31,X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_22,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r2_hidden(esk1_0,k3_xboole_0(k1_relat_1(esk3_0),esk2_0))
    & k1_funct_1(k7_relat_1(esk3_0,esk2_0),esk1_0) != k1_funct_1(esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_24,plain,
    ( k1_funct_1(X1,X2) = k1_funct_1(k5_relat_1(k6_relat_1(X3),X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k3_xboole_0(k1_relat_1(X1),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_0,k3_xboole_0(k1_relat_1(esk3_0),esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k1_funct_1(X1,X2) = k1_funct_1(k5_relat_1(k6_relat_1(X3),X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_0,k1_setfam_1(k6_enumset1(k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_36,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X3) = k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k4_xboole_0(k1_relat_1(X2),k4_xboole_0(k1_relat_1(X2),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk1_0,k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(k1_relat_1(esk3_0),esk2_0))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_40,plain,(
    ! [X39,X40] :
      ( ~ v1_relat_1(X40)
      | k7_relat_1(X40,X39) = k5_relat_1(k6_relat_1(X39),X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0),esk1_0) = k1_funct_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_42,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk3_0,esk2_0),esk1_0) != k1_funct_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_39])]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:25:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.033 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.39  fof(t71_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_funct_1)).
% 0.14/0.39  fof(t38_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(X3,X1)=k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_1)).
% 0.14/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.14/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.14/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.14/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.14/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.14/0.39  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.14/0.39  fof(c_0_11, plain, ![X37, X38]:k1_setfam_1(k2_tarski(X37,X38))=k3_xboole_0(X37,X38), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.39  fof(c_0_12, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.39  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1)))), inference(assume_negation,[status(cth)],[t71_funct_1])).
% 0.14/0.39  fof(c_0_14, plain, ![X41, X42, X43]:(~v1_relat_1(X43)|~v1_funct_1(X43)|(~r2_hidden(X41,k3_xboole_0(k1_relat_1(X43),X42))|k1_funct_1(X43,X41)=k1_funct_1(k5_relat_1(k6_relat_1(X42),X43),X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_funct_1])])).
% 0.14/0.39  cnf(c_0_15, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  fof(c_0_17, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.39  fof(c_0_18, plain, ![X15, X16, X17, X18]:k3_enumset1(X15,X15,X16,X17,X18)=k2_enumset1(X15,X16,X17,X18), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.14/0.39  fof(c_0_19, plain, ![X19, X20, X21, X22, X23]:k4_enumset1(X19,X19,X20,X21,X22,X23)=k3_enumset1(X19,X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.14/0.39  fof(c_0_20, plain, ![X24, X25, X26, X27, X28, X29]:k5_enumset1(X24,X24,X25,X26,X27,X28,X29)=k4_enumset1(X24,X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.14/0.39  fof(c_0_21, plain, ![X30, X31, X32, X33, X34, X35, X36]:k6_enumset1(X30,X30,X31,X32,X33,X34,X35,X36)=k5_enumset1(X30,X31,X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.14/0.39  fof(c_0_22, plain, ![X8, X9]:k4_xboole_0(X8,k4_xboole_0(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.14/0.39  fof(c_0_23, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(r2_hidden(esk1_0,k3_xboole_0(k1_relat_1(esk3_0),esk2_0))&k1_funct_1(k7_relat_1(esk3_0,esk2_0),esk1_0)!=k1_funct_1(esk3_0,esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.14/0.39  cnf(c_0_24, plain, (k1_funct_1(X1,X2)=k1_funct_1(k5_relat_1(k6_relat_1(X3),X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k3_xboole_0(k1_relat_1(X1),X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_25, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.39  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_27, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_28, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_29, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.39  cnf(c_0_30, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_32, negated_conjecture, (r2_hidden(esk1_0,k3_xboole_0(k1_relat_1(esk3_0),esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.39  cnf(c_0_33, plain, (k1_funct_1(X1,X2)=k1_funct_1(k5_relat_1(k6_relat_1(X3),X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.14/0.39  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.14/0.39  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_0,k1_setfam_1(k6_enumset1(k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.14/0.39  cnf(c_0_36, plain, (k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X3)=k1_funct_1(X2,X3)|~r2_hidden(X3,k4_xboole_0(k1_relat_1(X2),k4_xboole_0(k1_relat_1(X2),X1)))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.14/0.39  cnf(c_0_37, negated_conjecture, (r2_hidden(esk1_0,k4_xboole_0(k1_relat_1(esk3_0),k4_xboole_0(k1_relat_1(esk3_0),esk2_0)))), inference(rw,[status(thm)],[c_0_35, c_0_34])).
% 0.14/0.39  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.39  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.39  fof(c_0_40, plain, ![X39, X40]:(~v1_relat_1(X40)|k7_relat_1(X40,X39)=k5_relat_1(k6_relat_1(X39),X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.14/0.39  cnf(c_0_41, negated_conjecture, (k1_funct_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0),esk1_0)=k1_funct_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])])).
% 0.14/0.39  cnf(c_0_42, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.39  cnf(c_0_43, negated_conjecture, (k1_funct_1(k7_relat_1(esk3_0,esk2_0),esk1_0)!=k1_funct_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.39  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_39])]), c_0_43]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 45
% 0.14/0.39  # Proof object clause steps            : 22
% 0.14/0.39  # Proof object formula steps           : 23
% 0.14/0.39  # Proof object conjectures             : 11
% 0.14/0.39  # Proof object clause conjectures      : 8
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 14
% 0.14/0.39  # Proof object initial formulas used   : 11
% 0.14/0.39  # Proof object generating inferences   : 2
% 0.14/0.39  # Proof object simplifying inferences  : 27
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 11
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 14
% 0.14/0.39  # Removed in clause preprocessing      : 7
% 0.14/0.39  # Initial clauses in saturation        : 7
% 0.14/0.39  # Processed clauses                    : 15
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 0
% 0.14/0.39  # ...remaining for further processing  : 15
% 0.14/0.39  # Other redundant clauses eliminated   : 0
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 1
% 0.14/0.39  # Generated clauses                    : 2
% 0.14/0.39  # ...of the previous two non-trivial   : 2
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 2
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 0
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 7
% 0.14/0.39  #    Positive orientable unit clauses  : 4
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 1
% 0.14/0.39  #    Non-unit-clauses                  : 2
% 0.14/0.39  # Current number of unprocessed clauses: 1
% 0.14/0.39  # ...number of literals in the above   : 1
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 15
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 6
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 4
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.39  # Unit Clause-clause subsumption calls : 0
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 1
% 0.14/0.39  # BW rewrite match successes           : 1
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 873
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.035 s
% 0.14/0.39  # System time              : 0.003 s
% 0.14/0.39  # Total time               : 0.038 s
% 0.14/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
