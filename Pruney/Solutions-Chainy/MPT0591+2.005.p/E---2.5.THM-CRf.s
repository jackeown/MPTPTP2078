%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:07 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   37 (  58 expanded)
%              Number of clauses        :   20 (  25 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 144 expanded)
%              Number of equality atoms :   27 (  59 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t139_zfmisc_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2,X3,X4] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
            | r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)) )
         => r1_tarski(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(t195_relat_1,conjecture,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t193_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

fof(t194_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_8,plain,(
    ! [X18] :
      ( ~ v1_relat_1(X18)
      | r1_tarski(X18,k2_zfmisc_1(k1_relat_1(X18),k2_relat_1(X18))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

fof(c_0_9,plain,(
    ! [X12,X13] : v1_relat_1(k2_zfmisc_1(X12,X13)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_10,plain,(
    ! [X8,X9,X10,X11] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X8,X9),k2_zfmisc_1(X10,X11))
        | r1_tarski(X9,X11)
        | v1_xboole_0(X8) )
      & ( ~ r1_tarski(k2_zfmisc_1(X9,X8),k2_zfmisc_1(X11,X10))
        | r1_tarski(X9,X11)
        | v1_xboole_0(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t139_zfmisc_1])])])])])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
              & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t195_relat_1])).

fof(c_0_14,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X3)
    | v1_xboole_0(X2)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X1,X2)),k2_relat_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_17,plain,(
    ! [X14,X15] : r1_tarski(k1_relat_1(k2_zfmisc_1(X14,X15)),X14) ),
    inference(variable_rename,[status(thm)],[t193_relat_1])).

fof(c_0_18,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & ( k1_relat_1(k2_zfmisc_1(esk1_0,esk2_0)) != esk1_0
      | k2_relat_1(k2_zfmisc_1(esk1_0,esk2_0)) != esk2_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_19,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(X2,X4)
    | v1_xboole_0(X1)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_23,plain,(
    ! [X16,X17] : r1_tarski(k2_relat_1(k2_zfmisc_1(X16,X17)),X17) ),
    inference(variable_rename,[status(thm)],[t194_relat_1])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk1_0,esk2_0)) != esk1_0
    | k2_relat_1(k2_zfmisc_1(esk1_0,esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X2,X1)))
    | v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_16])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_29,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | k2_relat_1(k2_zfmisc_1(esk1_0,esk2_0)) != esk2_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_26]),c_0_27])])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( v1_xboole_0(esk1_0)
    | v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( v1_xboole_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_35,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_34]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:51:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053N
% 0.14/0.37  # and selection function HSelectMinInfpos.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.027 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 0.14/0.37  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.14/0.37  fof(t139_zfmisc_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2, X3, X4]:((r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)))=>r1_tarski(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 0.14/0.37  fof(t195_relat_1, conjecture, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 0.14/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.37  fof(t193_relat_1, axiom, ![X1, X2]:r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 0.14/0.37  fof(t194_relat_1, axiom, ![X1, X2]:r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 0.14/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.14/0.37  fof(c_0_8, plain, ![X18]:(~v1_relat_1(X18)|r1_tarski(X18,k2_zfmisc_1(k1_relat_1(X18),k2_relat_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.14/0.37  fof(c_0_9, plain, ![X12, X13]:v1_relat_1(k2_zfmisc_1(X12,X13)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.14/0.37  fof(c_0_10, plain, ![X8, X9, X10, X11]:((~r1_tarski(k2_zfmisc_1(X8,X9),k2_zfmisc_1(X10,X11))|r1_tarski(X9,X11)|v1_xboole_0(X8))&(~r1_tarski(k2_zfmisc_1(X9,X8),k2_zfmisc_1(X11,X10))|r1_tarski(X9,X11)|v1_xboole_0(X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t139_zfmisc_1])])])])])).
% 0.14/0.37  cnf(c_0_11, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_12, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  fof(c_0_13, negated_conjecture, ~(![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2))))), inference(assume_negation,[status(cth)],[t195_relat_1])).
% 0.14/0.37  fof(c_0_14, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.37  cnf(c_0_15, plain, (r1_tarski(X1,X3)|v1_xboole_0(X2)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_16, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X1,X2)),k2_relat_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.14/0.37  fof(c_0_17, plain, ![X14, X15]:r1_tarski(k1_relat_1(k2_zfmisc_1(X14,X15)),X14), inference(variable_rename,[status(thm)],[t193_relat_1])).
% 0.14/0.37  fof(c_0_18, negated_conjecture, ((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&(k1_relat_1(k2_zfmisc_1(esk1_0,esk2_0))!=esk1_0|k2_relat_1(k2_zfmisc_1(esk1_0,esk2_0))!=esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.14/0.37  cnf(c_0_19, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_20, plain, (r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X1,X2)))|v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.37  cnf(c_0_21, plain, (r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_22, plain, (r1_tarski(X2,X4)|v1_xboole_0(X1)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  fof(c_0_23, plain, ![X16, X17]:r1_tarski(k2_relat_1(k2_zfmisc_1(X16,X17)),X17), inference(variable_rename,[status(thm)],[t194_relat_1])).
% 0.14/0.37  cnf(c_0_24, negated_conjecture, (k1_relat_1(k2_zfmisc_1(esk1_0,esk2_0))!=esk1_0|k2_relat_1(k2_zfmisc_1(esk1_0,esk2_0))!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.37  cnf(c_0_25, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.14/0.37  cnf(c_0_26, plain, (r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X2,X1)))|v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_22, c_0_16])).
% 0.14/0.37  cnf(c_0_27, plain, (r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.37  fof(c_0_28, plain, ![X5]:(~v1_xboole_0(X5)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.14/0.37  cnf(c_0_29, negated_conjecture, (v1_xboole_0(esk2_0)|k2_relat_1(k2_zfmisc_1(esk1_0,esk2_0))!=esk2_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.14/0.37  cnf(c_0_30, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_26]), c_0_27])])).
% 0.14/0.37  cnf(c_0_31, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.37  cnf(c_0_32, negated_conjecture, (v1_xboole_0(esk1_0)|v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.37  cnf(c_0_33, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.37  cnf(c_0_34, negated_conjecture, (v1_xboole_0(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.14/0.37  cnf(c_0_35, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.37  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_34]), c_0_35]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 37
% 0.14/0.37  # Proof object clause steps            : 20
% 0.14/0.37  # Proof object formula steps           : 17
% 0.14/0.37  # Proof object conjectures             : 10
% 0.14/0.37  # Proof object clause conjectures      : 7
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 11
% 0.14/0.37  # Proof object initial formulas used   : 8
% 0.14/0.37  # Proof object generating inferences   : 9
% 0.14/0.37  # Proof object simplifying inferences  : 6
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 8
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 13
% 0.14/0.37  # Removed in clause preprocessing      : 0
% 0.14/0.37  # Initial clauses in saturation        : 13
% 0.14/0.37  # Processed clauses                    : 37
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 1
% 0.14/0.37  # ...remaining for further processing  : 36
% 0.14/0.37  # Other redundant clauses eliminated   : 2
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 1
% 0.14/0.37  # Generated clauses                    : 26
% 0.14/0.37  # ...of the previous two non-trivial   : 18
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 24
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 2
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 21
% 0.14/0.37  #    Positive orientable unit clauses  : 6
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 2
% 0.14/0.37  #    Non-unit-clauses                  : 13
% 0.14/0.37  # Current number of unprocessed clauses: 6
% 0.14/0.37  # ...number of literals in the above   : 12
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 13
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 19
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 19
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.37  # Unit Clause-clause subsumption calls : 7
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 1
% 0.14/0.37  # BW rewrite match successes           : 1
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 1005
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.029 s
% 0.14/0.37  # System time              : 0.002 s
% 0.14/0.37  # Total time               : 0.031 s
% 0.14/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
