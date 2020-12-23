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
% DateTime   : Thu Dec  3 10:59:31 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 179 expanded)
%              Number of clauses        :   21 (  79 expanded)
%              Number of leaves         :    6 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :   81 ( 552 expanded)
%              Number of equality atoms :   29 ( 220 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_mcart_1,conjecture,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ! [X3] :
              ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
             => X3 = k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc10_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & ~ ! [X3] :
                ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
               => X3 = k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t24_mcart_1])).

fof(c_0_7,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X15,X14)
        | r2_hidden(X15,X14)
        | v1_xboole_0(X14) )
      & ( ~ r2_hidden(X15,X14)
        | m1_subset_1(X15,X14)
        | v1_xboole_0(X14) )
      & ( ~ m1_subset_1(X15,X14)
        | v1_xboole_0(X15)
        | ~ v1_xboole_0(X14) )
      & ( ~ v1_xboole_0(X15)
        | m1_subset_1(X15,X14)
        | ~ v1_xboole_0(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_8,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & m1_subset_1(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))
    & esk5_0 != k4_tarski(k1_mcart_1(esk5_0),k2_mcart_1(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X9,X10,X11] :
      ( ~ r2_hidden(X9,k2_zfmisc_1(X10,X11))
      | k4_tarski(esk1_1(X9),esk2_1(X9)) = X9 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk5_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X18,X19] :
      ( k1_mcart_1(k4_tarski(X18,X19)) = X18
      & k2_mcart_1(k4_tarski(X18,X19)) = X19 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_13,plain,
    ( k4_tarski(esk1_1(X1),esk2_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))
    | v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( k4_tarski(esk1_1(esk5_0),esk2_1(esk5_0)) = esk5_0
    | v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( esk1_1(esk5_0) = k1_mcart_1(esk5_0)
    | v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_18,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | X6 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_20,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk5_0),esk2_1(esk5_0)) = esk5_0
    | v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( esk2_1(esk5_0) = k2_mcart_1(esk5_0)
    | v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( esk5_0 != k4_tarski(k1_mcart_1(esk5_0),k2_mcart_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

fof(c_0_25,plain,(
    ! [X16,X17] :
      ( v1_xboole_0(X16)
      | v1_xboole_0(X17)
      | ~ v1_xboole_0(k2_zfmisc_1(X16,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc10_subset_1])])])).

cnf(c_0_26,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_26]),c_0_28])])).

cnf(c_0_30,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_29]),c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_31]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:53:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.14/0.38  # and selection function SelectDiffNegLit.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t24_mcart_1, conjecture, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~(![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>X3=k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 0.14/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.14/0.38  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.14/0.38  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.14/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.14/0.38  fof(fc10_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>~(v1_xboole_0(k2_zfmisc_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_subset_1)).
% 0.14/0.38  fof(c_0_6, negated_conjecture, ~(![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~(![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>X3=k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3))))))), inference(assume_negation,[status(cth)],[t24_mcart_1])).
% 0.14/0.38  fof(c_0_7, plain, ![X14, X15]:(((~m1_subset_1(X15,X14)|r2_hidden(X15,X14)|v1_xboole_0(X14))&(~r2_hidden(X15,X14)|m1_subset_1(X15,X14)|v1_xboole_0(X14)))&((~m1_subset_1(X15,X14)|v1_xboole_0(X15)|~v1_xboole_0(X14))&(~v1_xboole_0(X15)|m1_subset_1(X15,X14)|~v1_xboole_0(X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&(m1_subset_1(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))&esk5_0!=k4_tarski(k1_mcart_1(esk5_0),k2_mcart_1(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.14/0.38  fof(c_0_9, plain, ![X9, X10, X11]:(~r2_hidden(X9,k2_zfmisc_1(X10,X11))|k4_tarski(esk1_1(X9),esk2_1(X9))=X9), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.14/0.38  cnf(c_0_10, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  fof(c_0_12, plain, ![X18, X19]:(k1_mcart_1(k4_tarski(X18,X19))=X18&k2_mcart_1(k4_tarski(X18,X19))=X19), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.14/0.38  cnf(c_0_13, plain, (k4_tarski(esk1_1(X1),esk2_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (r2_hidden(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))|v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.14/0.38  cnf(c_0_15, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (k4_tarski(esk1_1(esk5_0),esk2_1(esk5_0))=esk5_0|v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (esk1_1(esk5_0)=k1_mcart_1(esk5_0)|v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.38  cnf(c_0_18, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  fof(c_0_19, plain, ![X6]:(~v1_xboole_0(X6)|X6=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (k4_tarski(k1_mcart_1(esk5_0),esk2_1(esk5_0))=esk5_0|v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (esk2_1(esk5_0)=k2_mcart_1(esk5_0)|v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_18, c_0_16])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (esk5_0!=k4_tarski(k1_mcart_1(esk5_0),k2_mcart_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_23, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.14/0.38  fof(c_0_25, plain, ![X16, X17]:(v1_xboole_0(X16)|v1_xboole_0(X17)|~v1_xboole_0(k2_zfmisc_1(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc10_subset_1])])])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.38  cnf(c_0_27, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_xboole_0(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_24, c_0_26])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (v1_xboole_0(esk3_0)|v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_26]), c_0_28])])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (v1_xboole_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_29]), c_0_30])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_31]), c_0_32]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 34
% 0.14/0.39  # Proof object clause steps            : 21
% 0.14/0.39  # Proof object formula steps           : 13
% 0.14/0.39  # Proof object conjectures             : 18
% 0.14/0.39  # Proof object clause conjectures      : 15
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 10
% 0.14/0.39  # Proof object initial formulas used   : 6
% 0.14/0.39  # Proof object generating inferences   : 10
% 0.14/0.39  # Proof object simplifying inferences  : 6
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 7
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 14
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 14
% 0.14/0.39  # Processed clauses                    : 48
% 0.14/0.39  # ...of these trivial                  : 1
% 0.14/0.39  # ...subsumed                          : 0
% 0.14/0.39  # ...remaining for further processing  : 47
% 0.14/0.39  # Other redundant clauses eliminated   : 0
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 14
% 0.14/0.39  # Generated clauses                    : 33
% 0.14/0.39  # ...of the previous two non-trivial   : 31
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 33
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
% 0.14/0.39  # Current number of processed clauses  : 19
% 0.14/0.39  #    Positive orientable unit clauses  : 7
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 4
% 0.14/0.39  #    Non-unit-clauses                  : 8
% 0.14/0.39  # Current number of unprocessed clauses: 5
% 0.14/0.39  # ...number of literals in the above   : 11
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 28
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 32
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 32
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.39  # Unit Clause-clause subsumption calls : 20
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 4
% 0.14/0.39  # BW rewrite match successes           : 4
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 1145
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.029 s
% 0.14/0.39  # System time              : 0.003 s
% 0.14/0.39  # Total time               : 0.032 s
% 0.14/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
