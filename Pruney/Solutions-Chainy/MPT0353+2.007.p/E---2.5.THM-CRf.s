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
% DateTime   : Thu Dec  3 10:45:43 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 118 expanded)
%              Number of clauses        :   31 (  51 expanded)
%              Number of leaves         :   12 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  121 ( 210 expanded)
%              Number of equality atoms :   42 ( 102 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t32_subset_1])).

fof(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & k7_subset_1(esk2_0,esk3_0,esk4_0) != k9_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | k3_subset_1(X22,X23) = k4_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_15,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X30))
      | k9_subset_1(X30,X31,X32) = k3_xboole_0(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_16,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_17,plain,(
    ! [X10,X11,X12] : k3_xboole_0(X10,k4_xboole_0(X11,X12)) = k4_xboole_0(k3_xboole_0(X10,X11),X12) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_18,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_19,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k3_xboole_0(X6,X7) = X6 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_20,negated_conjecture,
    ( k7_subset_1(esk2_0,esk3_0,esk4_0) != k9_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( k9_subset_1(esk2_0,esk3_0,k4_xboole_0(esk2_0,esk4_0)) != k7_subset_1(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_29,plain,
    ( k9_subset_1(X2,X3,X1) = k4_xboole_0(X3,k4_xboole_0(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_24]),c_0_24])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_24]),c_0_24])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk4_0))) != k7_subset_1(esk2_0,esk3_0,esk4_0)
    | ~ m1_subset_1(k4_xboole_0(esk2_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_30])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0))) != k7_subset_1(esk2_0,esk3_0,esk4_0)
    | ~ m1_subset_1(k4_xboole_0(esk2_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_35])).

fof(c_0_38,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | k7_subset_1(X27,X28,X29) = k4_xboole_0(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_39,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | m1_subset_1(k3_subset_1(X24,X25),k1_zfmisc_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_40,negated_conjecture,
    ( k7_subset_1(esk2_0,esk3_0,esk4_0) != k4_xboole_0(esk3_0,esk4_0)
    | ~ m1_subset_1(k4_xboole_0(esk2_0,esk4_0),k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_43,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_44,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | r1_tarski(X15,X13)
        | X14 != k1_zfmisc_1(X13) )
      & ( ~ r1_tarski(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k1_zfmisc_1(X13) )
      & ( ~ r2_hidden(esk1_2(X17,X18),X18)
        | ~ r1_tarski(esk1_2(X17,X18),X17)
        | X18 = k1_zfmisc_1(X17) )
      & ( r2_hidden(esk1_2(X17,X18),X18)
        | r1_tarski(esk1_2(X17,X18),X17)
        | X18 = k1_zfmisc_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_45,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X21,X20)
        | r2_hidden(X21,X20)
        | v1_xboole_0(X20) )
      & ( ~ r2_hidden(X21,X20)
        | m1_subset_1(X21,X20)
        | v1_xboole_0(X20) )
      & ( ~ m1_subset_1(X21,X20)
        | v1_xboole_0(X21)
        | ~ v1_xboole_0(X20) )
      & ( ~ v1_xboole_0(X21)
        | m1_subset_1(X21,X20)
        | ~ v1_xboole_0(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_46,plain,(
    ! [X26] : ~ v1_xboole_0(k1_zfmisc_1(X26)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_47,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(esk2_0,esk4_0),k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_48,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_21])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_22])])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_42]),c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.30  % Computer   : n024.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 14:59:21 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  # Version: 2.5pre002
% 0.10/0.30  # No SInE strategy applied
% 0.10/0.30  # Trying AutoSched0 for 299 seconds
% 0.16/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.16/0.35  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.16/0.35  #
% 0.16/0.35  # Preprocessing time       : 0.019 s
% 0.16/0.35  # Presaturation interreduction done
% 0.16/0.35  
% 0.16/0.35  # Proof found!
% 0.16/0.35  # SZS status Theorem
% 0.16/0.35  # SZS output start CNFRefutation
% 0.16/0.35  fof(t32_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 0.16/0.35  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.16/0.35  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.16/0.35  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.16/0.35  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.16/0.35  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.16/0.35  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.16/0.35  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.16/0.35  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.16/0.35  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.16/0.35  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.16/0.35  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.16/0.35  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3))))), inference(assume_negation,[status(cth)],[t32_subset_1])).
% 0.16/0.35  fof(c_0_13, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&k7_subset_1(esk2_0,esk3_0,esk4_0)!=k9_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.16/0.35  fof(c_0_14, plain, ![X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|k3_subset_1(X22,X23)=k4_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.16/0.35  fof(c_0_15, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(X30))|k9_subset_1(X30,X31,X32)=k3_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.16/0.35  fof(c_0_16, plain, ![X8, X9]:k4_xboole_0(X8,k4_xboole_0(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.16/0.35  fof(c_0_17, plain, ![X10, X11, X12]:k3_xboole_0(X10,k4_xboole_0(X11,X12))=k4_xboole_0(k3_xboole_0(X10,X11),X12), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.16/0.35  fof(c_0_18, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.16/0.35  fof(c_0_19, plain, ![X6, X7]:(~r1_tarski(X6,X7)|k3_xboole_0(X6,X7)=X6), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.16/0.35  cnf(c_0_20, negated_conjecture, (k7_subset_1(esk2_0,esk3_0,esk4_0)!=k9_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.16/0.35  cnf(c_0_21, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.16/0.35  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.16/0.35  cnf(c_0_23, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.16/0.35  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.16/0.35  cnf(c_0_25, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.16/0.35  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.16/0.35  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.16/0.35  cnf(c_0_28, negated_conjecture, (k9_subset_1(esk2_0,esk3_0,k4_xboole_0(esk2_0,esk4_0))!=k7_subset_1(esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.16/0.35  cnf(c_0_29, plain, (k9_subset_1(X2,X3,X1)=k4_xboole_0(X3,k4_xboole_0(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.16/0.35  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_24]), c_0_24])).
% 0.16/0.35  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_24]), c_0_24])).
% 0.16/0.35  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_24])).
% 0.16/0.35  cnf(c_0_33, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk4_0)))!=k7_subset_1(esk2_0,esk3_0,esk4_0)|~m1_subset_1(k4_xboole_0(esk2_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.16/0.35  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_30])).
% 0.16/0.35  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.16/0.35  cnf(c_0_36, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk4_0)))!=k7_subset_1(esk2_0,esk3_0,esk4_0)|~m1_subset_1(k4_xboole_0(esk2_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.16/0.35  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(X2,X3)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_30, c_0_35])).
% 0.16/0.35  fof(c_0_38, plain, ![X27, X28, X29]:(~m1_subset_1(X28,k1_zfmisc_1(X27))|k7_subset_1(X27,X28,X29)=k4_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.16/0.35  fof(c_0_39, plain, ![X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|m1_subset_1(k3_subset_1(X24,X25),k1_zfmisc_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.16/0.35  cnf(c_0_40, negated_conjecture, (k7_subset_1(esk2_0,esk3_0,esk4_0)!=k4_xboole_0(esk3_0,esk4_0)|~m1_subset_1(k4_xboole_0(esk2_0,esk4_0),k1_zfmisc_1(esk2_0))|~r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.16/0.35  cnf(c_0_41, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.16/0.35  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.16/0.35  cnf(c_0_43, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.16/0.35  fof(c_0_44, plain, ![X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X15,X14)|r1_tarski(X15,X13)|X14!=k1_zfmisc_1(X13))&(~r1_tarski(X16,X13)|r2_hidden(X16,X14)|X14!=k1_zfmisc_1(X13)))&((~r2_hidden(esk1_2(X17,X18),X18)|~r1_tarski(esk1_2(X17,X18),X17)|X18=k1_zfmisc_1(X17))&(r2_hidden(esk1_2(X17,X18),X18)|r1_tarski(esk1_2(X17,X18),X17)|X18=k1_zfmisc_1(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.16/0.35  fof(c_0_45, plain, ![X20, X21]:(((~m1_subset_1(X21,X20)|r2_hidden(X21,X20)|v1_xboole_0(X20))&(~r2_hidden(X21,X20)|m1_subset_1(X21,X20)|v1_xboole_0(X20)))&((~m1_subset_1(X21,X20)|v1_xboole_0(X21)|~v1_xboole_0(X20))&(~v1_xboole_0(X21)|m1_subset_1(X21,X20)|~v1_xboole_0(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.16/0.35  fof(c_0_46, plain, ![X26]:~v1_xboole_0(k1_zfmisc_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.16/0.35  cnf(c_0_47, negated_conjecture, (~m1_subset_1(k4_xboole_0(esk2_0,esk4_0),k1_zfmisc_1(esk2_0))|~r1_tarski(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.16/0.35  cnf(c_0_48, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_21])).
% 0.16/0.35  cnf(c_0_49, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.16/0.35  cnf(c_0_50, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.16/0.35  cnf(c_0_51, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.16/0.35  cnf(c_0_52, negated_conjecture, (~r1_tarski(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_22])])).
% 0.16/0.35  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_49])).
% 0.16/0.35  cnf(c_0_54, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_42]), c_0_51])).
% 0.16/0.35  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])]), ['proof']).
% 0.16/0.35  # SZS output end CNFRefutation
% 0.16/0.35  # Proof object total steps             : 56
% 0.16/0.35  # Proof object clause steps            : 31
% 0.16/0.35  # Proof object formula steps           : 25
% 0.16/0.35  # Proof object conjectures             : 14
% 0.16/0.35  # Proof object clause conjectures      : 11
% 0.16/0.35  # Proof object formula conjectures     : 3
% 0.16/0.35  # Proof object initial clauses used    : 14
% 0.16/0.35  # Proof object initial formulas used   : 12
% 0.16/0.35  # Proof object generating inferences   : 11
% 0.16/0.35  # Proof object simplifying inferences  : 18
% 0.16/0.35  # Training examples: 0 positive, 0 negative
% 0.16/0.35  # Parsed axioms                        : 12
% 0.16/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.35  # Initial clauses                      : 20
% 0.16/0.35  # Removed in clause preprocessing      : 1
% 0.16/0.35  # Initial clauses in saturation        : 19
% 0.16/0.35  # Processed clauses                    : 274
% 0.16/0.35  # ...of these trivial                  : 1
% 0.16/0.35  # ...subsumed                          : 123
% 0.16/0.35  # ...remaining for further processing  : 150
% 0.16/0.35  # Other redundant clauses eliminated   : 2
% 0.16/0.35  # Clauses deleted for lack of memory   : 0
% 0.16/0.35  # Backward-subsumed                    : 3
% 0.16/0.35  # Backward-rewritten                   : 1
% 0.16/0.35  # Generated clauses                    : 2033
% 0.16/0.35  # ...of the previous two non-trivial   : 1992
% 0.16/0.35  # Contextual simplify-reflections      : 0
% 0.16/0.35  # Paramodulations                      : 2031
% 0.16/0.35  # Factorizations                       : 0
% 0.16/0.35  # Equation resolutions                 : 2
% 0.16/0.35  # Propositional unsat checks           : 0
% 0.16/0.35  #    Propositional check models        : 0
% 0.16/0.35  #    Propositional check unsatisfiable : 0
% 0.16/0.35  #    Propositional clauses             : 0
% 0.16/0.35  #    Propositional clauses after purity: 0
% 0.16/0.35  #    Propositional unsat core size     : 0
% 0.16/0.35  #    Propositional preprocessing time  : 0.000
% 0.16/0.35  #    Propositional encoding time       : 0.000
% 0.16/0.35  #    Propositional solver time         : 0.000
% 0.16/0.35  #    Success case prop preproc time    : 0.000
% 0.16/0.35  #    Success case prop encoding time   : 0.000
% 0.16/0.35  #    Success case prop solver time     : 0.000
% 0.16/0.35  # Current number of processed clauses  : 125
% 0.16/0.35  #    Positive orientable unit clauses  : 6
% 0.16/0.35  #    Positive unorientable unit clauses: 4
% 0.16/0.35  #    Negative unit clauses             : 4
% 0.16/0.35  #    Non-unit-clauses                  : 111
% 0.16/0.35  # Current number of unprocessed clauses: 1756
% 0.16/0.35  # ...number of literals in the above   : 4926
% 0.16/0.35  # Current number of archived formulas  : 0
% 0.16/0.35  # Current number of archived clauses   : 24
% 0.16/0.35  # Clause-clause subsumption calls (NU) : 2558
% 0.16/0.35  # Rec. Clause-clause subsumption calls : 1618
% 0.16/0.35  # Non-unit clause-clause subsumptions  : 117
% 0.16/0.35  # Unit Clause-clause subsumption calls : 32
% 0.16/0.35  # Rewrite failures with RHS unbound    : 0
% 0.16/0.35  # BW rewrite match attempts            : 78
% 0.16/0.35  # BW rewrite match successes           : 25
% 0.16/0.35  # Condensation attempts                : 0
% 0.16/0.35  # Condensation successes               : 0
% 0.16/0.35  # Termbank termtop insertions          : 34267
% 0.16/0.35  
% 0.16/0.35  # -------------------------------------------------
% 0.16/0.35  # User time                : 0.043 s
% 0.16/0.35  # System time              : 0.006 s
% 0.16/0.35  # Total time               : 0.049 s
% 0.16/0.35  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
