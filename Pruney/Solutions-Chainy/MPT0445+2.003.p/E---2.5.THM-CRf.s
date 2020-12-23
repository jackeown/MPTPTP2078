%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:19 EST 2020

% Result     : Theorem 6.28s
% Output     : CNFRefutation 6.28s
% Verified   : 
% Statistics : Number of formulae       :   43 (  86 expanded)
%              Number of clauses        :   24 (  37 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :   73 ( 150 expanded)
%              Number of equality atoms :   15 (  37 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t28_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t26_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(c_0_9,plain,(
    ! [X14,X15] : r1_tarski(X14,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_10,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_11,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,k2_xboole_0(X12,X13))
      | r1_tarski(k4_xboole_0(X11,X12),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_15,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t28_relat_1])).

fof(c_0_18,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | v1_relat_1(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_21,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ v1_relat_1(X27)
      | k2_relat_1(k2_xboole_0(X26,X27)) = k2_xboole_0(k2_relat_1(X26),k2_relat_1(X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & ~ r1_tarski(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_23,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( k2_xboole_0(k2_relat_1(X1),k2_relat_1(esk2_0)) = k2_relat_1(k2_xboole_0(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(k4_xboole_0(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( k2_xboole_0(k2_relat_1(esk2_0),k2_relat_1(k4_xboole_0(esk1_0,X1))) = k2_relat_1(k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_13]),c_0_13])).

fof(c_0_32,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k4_xboole_0(X10,X9)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_33,plain,(
    ! [X16,X17] : k6_subset_1(X16,X17) = k4_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,X2)))
    | ~ r1_tarski(X1,k2_relat_1(k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_31])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k2_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk1_0)) = k2_relat_1(k2_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_13]),c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,esk2_0)))
    | ~ r1_tarski(X1,k2_relat_1(k2_xboole_0(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k2_xboole_0(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 6.28/6.46  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 6.28/6.46  # and selection function SelectDiffNegLit.
% 6.28/6.46  #
% 6.28/6.46  # Preprocessing time       : 0.027 s
% 6.28/6.46  # Presaturation interreduction done
% 6.28/6.46  
% 6.28/6.46  # Proof found!
% 6.28/6.46  # SZS status Theorem
% 6.28/6.46  # SZS output start CNFRefutation
% 6.28/6.46  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.28/6.46  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.28/6.46  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 6.28/6.46  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.28/6.46  fof(t28_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relat_1)).
% 6.28/6.46  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.28/6.46  fof(t26_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_relat_1)).
% 6.28/6.46  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.28/6.46  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 6.28/6.46  fof(c_0_9, plain, ![X14, X15]:r1_tarski(X14,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 6.28/6.46  fof(c_0_10, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 6.28/6.46  fof(c_0_11, plain, ![X11, X12, X13]:(~r1_tarski(X11,k2_xboole_0(X12,X13))|r1_tarski(k4_xboole_0(X11,X12),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 6.28/6.46  cnf(c_0_12, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 6.28/6.46  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 6.28/6.46  fof(c_0_14, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 6.28/6.46  cnf(c_0_15, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 6.28/6.46  cnf(c_0_16, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 6.28/6.46  fof(c_0_17, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t28_relat_1])).
% 6.28/6.46  fof(c_0_18, plain, ![X20, X21]:(~v1_relat_1(X20)|(~m1_subset_1(X21,k1_zfmisc_1(X20))|v1_relat_1(X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 6.28/6.46  cnf(c_0_19, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.28/6.46  cnf(c_0_20, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 6.28/6.46  fof(c_0_21, plain, ![X26, X27]:(~v1_relat_1(X26)|(~v1_relat_1(X27)|k2_relat_1(k2_xboole_0(X26,X27))=k2_xboole_0(k2_relat_1(X26),k2_relat_1(X27)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).
% 6.28/6.46  fof(c_0_22, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&~r1_tarski(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 6.28/6.46  cnf(c_0_23, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.28/6.46  cnf(c_0_24, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 6.28/6.46  cnf(c_0_25, plain, (k2_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 6.28/6.46  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 6.28/6.46  cnf(c_0_27, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 6.28/6.46  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 6.28/6.46  cnf(c_0_29, negated_conjecture, (k2_xboole_0(k2_relat_1(X1),k2_relat_1(esk2_0))=k2_relat_1(k2_xboole_0(X1,esk2_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 6.28/6.46  cnf(c_0_30, negated_conjecture, (v1_relat_1(k4_xboole_0(esk1_0,X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 6.28/6.46  cnf(c_0_31, negated_conjecture, (k2_xboole_0(k2_relat_1(esk2_0),k2_relat_1(k4_xboole_0(esk1_0,X1)))=k2_relat_1(k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_13]), c_0_13])).
% 6.28/6.46  fof(c_0_32, plain, ![X9, X10]:k2_xboole_0(X9,k4_xboole_0(X10,X9))=k2_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 6.28/6.46  fof(c_0_33, plain, ![X16, X17]:k6_subset_1(X16,X17)=k4_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 6.28/6.46  cnf(c_0_34, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,X2)))|~r1_tarski(X1,k2_relat_1(k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,X2))))), inference(spm,[status(thm)],[c_0_15, c_0_31])).
% 6.28/6.46  cnf(c_0_35, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 6.28/6.46  cnf(c_0_36, negated_conjecture, (k2_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk1_0))=k2_relat_1(k2_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_13]), c_0_13])).
% 6.28/6.46  cnf(c_0_37, negated_conjecture, (~r1_tarski(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 6.28/6.46  cnf(c_0_38, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 6.28/6.46  cnf(c_0_39, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,esk2_0)))|~r1_tarski(X1,k2_relat_1(k2_xboole_0(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 6.28/6.46  cnf(c_0_40, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k2_xboole_0(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_16, c_0_36])).
% 6.28/6.46  cnf(c_0_41, negated_conjecture, (~r1_tarski(k4_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_38])).
% 6.28/6.46  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), ['proof']).
% 6.28/6.46  # SZS output end CNFRefutation
% 6.28/6.46  # Proof object total steps             : 43
% 6.28/6.46  # Proof object clause steps            : 24
% 6.28/6.46  # Proof object formula steps           : 19
% 6.28/6.46  # Proof object conjectures             : 15
% 6.28/6.46  # Proof object clause conjectures      : 12
% 6.28/6.46  # Proof object formula conjectures     : 3
% 6.28/6.46  # Proof object initial clauses used    : 11
% 6.28/6.46  # Proof object initial formulas used   : 9
% 6.28/6.46  # Proof object generating inferences   : 12
% 6.28/6.46  # Proof object simplifying inferences  : 7
% 6.28/6.46  # Training examples: 0 positive, 0 negative
% 6.28/6.46  # Parsed axioms                        : 12
% 6.28/6.46  # Removed by relevancy pruning/SinE    : 0
% 6.28/6.46  # Initial clauses                      : 16
% 6.28/6.46  # Removed in clause preprocessing      : 1
% 6.28/6.46  # Initial clauses in saturation        : 15
% 6.28/6.46  # Processed clauses                    : 5828
% 6.28/6.46  # ...of these trivial                  : 760
% 6.28/6.46  # ...subsumed                          : 1148
% 6.28/6.46  # ...remaining for further processing  : 3920
% 6.28/6.46  # Other redundant clauses eliminated   : 0
% 6.28/6.46  # Clauses deleted for lack of memory   : 0
% 6.28/6.46  # Backward-subsumed                    : 190
% 6.28/6.46  # Backward-rewritten                   : 217
% 6.28/6.46  # Generated clauses                    : 635797
% 6.28/6.46  # ...of the previous two non-trivial   : 626290
% 6.28/6.46  # Contextual simplify-reflections      : 45
% 6.28/6.46  # Paramodulations                      : 635797
% 6.28/6.46  # Factorizations                       : 0
% 6.28/6.46  # Equation resolutions                 : 0
% 6.28/6.46  # Propositional unsat checks           : 0
% 6.28/6.46  #    Propositional check models        : 0
% 6.28/6.46  #    Propositional check unsatisfiable : 0
% 6.28/6.46  #    Propositional clauses             : 0
% 6.28/6.46  #    Propositional clauses after purity: 0
% 6.28/6.46  #    Propositional unsat core size     : 0
% 6.28/6.46  #    Propositional preprocessing time  : 0.000
% 6.28/6.46  #    Propositional encoding time       : 0.000
% 6.28/6.46  #    Propositional solver time         : 0.000
% 6.28/6.46  #    Success case prop preproc time    : 0.000
% 6.28/6.46  #    Success case prop encoding time   : 0.000
% 6.28/6.46  #    Success case prop solver time     : 0.000
% 6.28/6.46  # Current number of processed clauses  : 3498
% 6.28/6.46  #    Positive orientable unit clauses  : 1698
% 6.28/6.46  #    Positive unorientable unit clauses: 1
% 6.28/6.46  #    Negative unit clauses             : 1
% 6.28/6.46  #    Non-unit-clauses                  : 1798
% 6.28/6.46  # Current number of unprocessed clauses: 618954
% 6.28/6.46  # ...number of literals in the above   : 631169
% 6.28/6.46  # Current number of archived formulas  : 0
% 6.28/6.46  # Current number of archived clauses   : 423
% 6.28/6.46  # Clause-clause subsumption calls (NU) : 252964
% 6.28/6.46  # Rec. Clause-clause subsumption calls : 238490
% 6.28/6.46  # Non-unit clause-clause subsumptions  : 1383
% 6.28/6.46  # Unit Clause-clause subsumption calls : 125546
% 6.28/6.46  # Rewrite failures with RHS unbound    : 0
% 6.28/6.46  # BW rewrite match attempts            : 66409
% 6.28/6.46  # BW rewrite match successes           : 213
% 6.28/6.46  # Condensation attempts                : 0
% 6.28/6.46  # Condensation successes               : 0
% 6.28/6.46  # Termbank termtop insertions          : 12504950
% 6.31/6.49  
% 6.31/6.49  # -------------------------------------------------
% 6.31/6.49  # User time                : 5.728 s
% 6.31/6.49  # System time              : 0.410 s
% 6.31/6.49  # Total time               : 6.138 s
% 6.31/6.49  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
