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
% DateTime   : Thu Dec  3 10:48:29 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 420 expanded)
%              Number of clauses        :   28 ( 187 expanded)
%              Number of leaves         :    9 ( 116 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 446 expanded)
%              Number of equality atoms :   47 ( 413 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fc5_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k1_tarski(k4_tarski(X1,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t82_enumset1,axiom,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(t35_zfmisc_1,axiom,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(t32_relat_1,conjecture,(
    ! [X1,X2] : k3_relat_1(k1_tarski(k4_tarski(X1,X2))) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relat_1)).

fof(t24_relat_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( v1_relat_1(X5)
     => ( X5 = k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))
       => ( k1_relat_1(X5) = k2_tarski(X1,X3)
          & k2_relat_1(X5) = k2_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relat_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t93_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(c_0_9,plain,(
    ! [X41,X42] : v1_relat_1(k1_tarski(k4_tarski(X41,X42))) ),
    inference(variable_rename,[status(thm)],[fc5_relat_1])).

fof(c_0_10,plain,(
    ! [X26] : k2_tarski(X26,X26) = k1_tarski(X26) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X27] : k2_enumset1(X27,X27,X27,X27) = k1_tarski(X27) ),
    inference(variable_rename,[status(thm)],[t82_enumset1])).

fof(c_0_12,plain,(
    ! [X30,X31] : k2_zfmisc_1(k1_tarski(X30),k1_tarski(X31)) = k1_tarski(k4_tarski(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t35_zfmisc_1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] : k3_relat_1(k1_tarski(k4_tarski(X1,X2))) = k2_tarski(X1,X2) ),
    inference(assume_negation,[status(cth)],[t32_relat_1])).

cnf(c_0_14,plain,
    ( v1_relat_1(k1_tarski(k4_tarski(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,negated_conjecture,(
    k3_relat_1(k1_tarski(k4_tarski(esk3_0,esk4_0))) != k2_tarski(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_19,plain,(
    ! [X43,X44,X45,X46,X47] :
      ( ( k1_relat_1(X47) = k2_tarski(X43,X45)
        | X47 != k2_tarski(k4_tarski(X43,X44),k4_tarski(X45,X46))
        | ~ v1_relat_1(X47) )
      & ( k2_relat_1(X47) = k2_tarski(X44,X46)
        | X47 != k2_tarski(k4_tarski(X43,X44),k4_tarski(X45,X46))
        | ~ v1_relat_1(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_relat_1])])])).

cnf(c_0_20,plain,
    ( v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k2_tarski(X1,X1) ),
    inference(rw,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_15]),c_0_15]),c_0_15])).

fof(c_0_23,plain,(
    ! [X24,X25] : k2_tarski(X24,X25) = k2_xboole_0(k1_tarski(X24),k1_tarski(X25)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_24,plain,(
    ! [X38,X39] : k3_tarski(k2_tarski(X38,X39)) = k2_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[t93_zfmisc_1])).

cnf(c_0_25,negated_conjecture,
    ( k3_relat_1(k1_tarski(k4_tarski(esk3_0,esk4_0))) != k2_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X40] :
      ( ~ v1_relat_1(X40)
      | k3_relat_1(X40) = k2_xboole_0(k1_relat_1(X40),k2_relat_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_27,plain,
    ( k1_relat_1(X1) = k2_tarski(X2,X3)
    | X1 != k2_tarski(k4_tarski(X2,X4),k4_tarski(X3,X5))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v1_relat_1(k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_30,plain,
    ( k2_relat_1(X1) = k2_tarski(X2,X3)
    | X1 != k2_tarski(k4_tarski(X4,X2),k4_tarski(X5,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( k3_relat_1(k2_tarski(k4_tarski(esk3_0,esk4_0),k4_tarski(esk3_0,esk4_0))) != k2_tarski(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_15])).

cnf(c_0_34,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) = k2_tarski(X1,X3)
    | ~ v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( k2_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) = k2_tarski(X2,X4)
    | ~ v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k2_tarski(X1,X2) = k3_tarski(k2_tarski(k2_tarski(X1,X1),k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_15]),c_0_15]),c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k3_relat_1(k2_enumset1(k4_tarski(esk3_0,esk4_0),k4_tarski(esk3_0,esk4_0),k4_tarski(esk3_0,esk4_0),k4_tarski(esk3_0,esk4_0))) != k2_tarski(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_21])).

cnf(c_0_40,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_41,plain,
    ( k1_relat_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))) = k2_enumset1(X1,X1,X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_21]),c_0_29]),c_0_21]),c_0_29]),c_0_36])])).

cnf(c_0_42,plain,
    ( k2_relat_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))) = k2_enumset1(X2,X2,X2,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_21]),c_0_29]),c_0_21]),c_0_29]),c_0_36])])).

cnf(c_0_43,plain,
    ( k3_tarski(k2_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))) = k2_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_21]),c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( k3_relat_1(k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) != k2_tarski(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_29])).

cnf(c_0_45,plain,
    ( k3_relat_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))) = k2_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:10:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S04AN
% 0.21/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.028 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(fc5_relat_1, axiom, ![X1, X2]:v1_relat_1(k1_tarski(k4_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_relat_1)).
% 0.21/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.40  fof(t82_enumset1, axiom, ![X1]:k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 0.21/0.40  fof(t35_zfmisc_1, axiom, ![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 0.21/0.40  fof(t32_relat_1, conjecture, ![X1, X2]:k3_relat_1(k1_tarski(k4_tarski(X1,X2)))=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relat_1)).
% 0.21/0.40  fof(t24_relat_1, axiom, ![X1, X2, X3, X4, X5]:(v1_relat_1(X5)=>(X5=k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))=>(k1_relat_1(X5)=k2_tarski(X1,X3)&k2_relat_1(X5)=k2_tarski(X2,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relat_1)).
% 0.21/0.40  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.21/0.40  fof(t93_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 0.21/0.40  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 0.21/0.40  fof(c_0_9, plain, ![X41, X42]:v1_relat_1(k1_tarski(k4_tarski(X41,X42))), inference(variable_rename,[status(thm)],[fc5_relat_1])).
% 0.21/0.40  fof(c_0_10, plain, ![X26]:k2_tarski(X26,X26)=k1_tarski(X26), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.40  fof(c_0_11, plain, ![X27]:k2_enumset1(X27,X27,X27,X27)=k1_tarski(X27), inference(variable_rename,[status(thm)],[t82_enumset1])).
% 0.21/0.40  fof(c_0_12, plain, ![X30, X31]:k2_zfmisc_1(k1_tarski(X30),k1_tarski(X31))=k1_tarski(k4_tarski(X30,X31)), inference(variable_rename,[status(thm)],[t35_zfmisc_1])).
% 0.21/0.40  fof(c_0_13, negated_conjecture, ~(![X1, X2]:k3_relat_1(k1_tarski(k4_tarski(X1,X2)))=k2_tarski(X1,X2)), inference(assume_negation,[status(cth)],[t32_relat_1])).
% 0.21/0.40  cnf(c_0_14, plain, (v1_relat_1(k1_tarski(k4_tarski(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.40  cnf(c_0_15, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.40  cnf(c_0_16, plain, (k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.40  cnf(c_0_17, plain, (k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  fof(c_0_18, negated_conjecture, k3_relat_1(k1_tarski(k4_tarski(esk3_0,esk4_0)))!=k2_tarski(esk3_0,esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.21/0.40  fof(c_0_19, plain, ![X43, X44, X45, X46, X47]:((k1_relat_1(X47)=k2_tarski(X43,X45)|X47!=k2_tarski(k4_tarski(X43,X44),k4_tarski(X45,X46))|~v1_relat_1(X47))&(k2_relat_1(X47)=k2_tarski(X44,X46)|X47!=k2_tarski(k4_tarski(X43,X44),k4_tarski(X45,X46))|~v1_relat_1(X47))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_relat_1])])])).
% 0.21/0.40  cnf(c_0_20, plain, (v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.21/0.40  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X1,X1)=k2_tarski(X1,X1)), inference(rw,[status(thm)],[c_0_16, c_0_15])).
% 0.21/0.40  cnf(c_0_22, plain, (k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_15]), c_0_15]), c_0_15])).
% 0.21/0.40  fof(c_0_23, plain, ![X24, X25]:k2_tarski(X24,X25)=k2_xboole_0(k1_tarski(X24),k1_tarski(X25)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.21/0.40  fof(c_0_24, plain, ![X38, X39]:k3_tarski(k2_tarski(X38,X39))=k2_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[t93_zfmisc_1])).
% 0.21/0.40  cnf(c_0_25, negated_conjecture, (k3_relat_1(k1_tarski(k4_tarski(esk3_0,esk4_0)))!=k2_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.40  fof(c_0_26, plain, ![X40]:(~v1_relat_1(X40)|k3_relat_1(X40)=k2_xboole_0(k1_relat_1(X40),k2_relat_1(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.21/0.40  cnf(c_0_27, plain, (k1_relat_1(X1)=k2_tarski(X2,X3)|X1!=k2_tarski(k4_tarski(X2,X4),k4_tarski(X3,X5))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.40  cnf(c_0_28, plain, (v1_relat_1(k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.40  cnf(c_0_29, plain, (k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2))=k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_21]), c_0_21]), c_0_21])).
% 0.21/0.40  cnf(c_0_30, plain, (k2_relat_1(X1)=k2_tarski(X2,X3)|X1!=k2_tarski(k4_tarski(X4,X2),k4_tarski(X5,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.40  cnf(c_0_31, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.40  cnf(c_0_32, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.40  cnf(c_0_33, negated_conjecture, (k3_relat_1(k2_tarski(k4_tarski(esk3_0,esk4_0),k4_tarski(esk3_0,esk4_0)))!=k2_tarski(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_25, c_0_15])).
% 0.21/0.40  cnf(c_0_34, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.40  cnf(c_0_35, plain, (k1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4)))=k2_tarski(X1,X3)|~v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4)))), inference(er,[status(thm)],[c_0_27])).
% 0.21/0.40  cnf(c_0_36, plain, (v1_relat_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.40  cnf(c_0_37, plain, (k2_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4)))=k2_tarski(X2,X4)|~v1_relat_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4)))), inference(er,[status(thm)],[c_0_30])).
% 0.21/0.40  cnf(c_0_38, plain, (k2_tarski(X1,X2)=k3_tarski(k2_tarski(k2_tarski(X1,X1),k2_tarski(X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_15]), c_0_15]), c_0_32])).
% 0.21/0.40  cnf(c_0_39, negated_conjecture, (k3_relat_1(k2_enumset1(k4_tarski(esk3_0,esk4_0),k4_tarski(esk3_0,esk4_0),k4_tarski(esk3_0,esk4_0),k4_tarski(esk3_0,esk4_0)))!=k2_tarski(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_33, c_0_21])).
% 0.21/0.40  cnf(c_0_40, plain, (k3_relat_1(X1)=k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_34, c_0_32])).
% 0.21/0.40  cnf(c_0_41, plain, (k1_relat_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))=k2_enumset1(X1,X1,X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_21]), c_0_29]), c_0_21]), c_0_29]), c_0_36])])).
% 0.21/0.40  cnf(c_0_42, plain, (k2_relat_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))=k2_enumset1(X2,X2,X2,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_21]), c_0_29]), c_0_21]), c_0_29]), c_0_36])])).
% 0.21/0.40  cnf(c_0_43, plain, (k3_tarski(k2_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))=k2_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_21]), c_0_21])).
% 0.21/0.40  cnf(c_0_44, negated_conjecture, (k3_relat_1(k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))!=k2_tarski(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_39, c_0_29])).
% 0.21/0.40  cnf(c_0_45, plain, (k3_relat_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))=k2_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_36]), c_0_41]), c_0_42]), c_0_43])).
% 0.21/0.40  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 47
% 0.21/0.40  # Proof object clause steps            : 28
% 0.21/0.40  # Proof object formula steps           : 19
% 0.21/0.40  # Proof object conjectures             : 8
% 0.21/0.40  # Proof object clause conjectures      : 5
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 10
% 0.21/0.40  # Proof object initial formulas used   : 9
% 0.21/0.40  # Proof object generating inferences   : 3
% 0.21/0.40  # Proof object simplifying inferences  : 36
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 15
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 28
% 0.21/0.40  # Removed in clause preprocessing      : 2
% 0.21/0.40  # Initial clauses in saturation        : 26
% 0.21/0.40  # Processed clauses                    : 259
% 0.21/0.40  # ...of these trivial                  : 17
% 0.21/0.40  # ...subsumed                          : 78
% 0.21/0.40  # ...remaining for further processing  : 164
% 0.21/0.40  # Other redundant clauses eliminated   : 56
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 1
% 0.21/0.40  # Backward-rewritten                   : 6
% 0.21/0.40  # Generated clauses                    : 766
% 0.21/0.40  # ...of the previous two non-trivial   : 681
% 0.21/0.40  # Contextual simplify-reflections      : 0
% 0.21/0.40  # Paramodulations                      : 685
% 0.21/0.40  # Factorizations                       : 28
% 0.21/0.40  # Equation resolutions                 : 56
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 122
% 0.21/0.40  #    Positive orientable unit clauses  : 20
% 0.21/0.40  #    Positive unorientable unit clauses: 1
% 0.21/0.40  #    Negative unit clauses             : 55
% 0.21/0.40  #    Non-unit-clauses                  : 46
% 0.21/0.40  # Current number of unprocessed clauses: 474
% 0.21/0.40  # ...number of literals in the above   : 1053
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 35
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 631
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 480
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 50
% 0.21/0.40  # Unit Clause-clause subsumption calls : 632
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 28
% 0.21/0.40  # BW rewrite match successes           : 11
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 15673
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.048 s
% 0.21/0.40  # System time              : 0.004 s
% 0.21/0.40  # Total time               : 0.053 s
% 0.21/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
