%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:09 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   46 (  82 expanded)
%              Number of clauses        :   25 (  35 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 143 expanded)
%              Number of equality atoms :   22 (  44 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t15_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(c_0_10,plain,(
    ! [X15,X16] : m1_subset_1(k6_subset_1(X15,X16),k1_zfmisc_1(X15)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_11,plain,(
    ! [X17,X18] : k6_subset_1(X17,X18) = k4_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t15_relat_1])).

fof(c_0_13,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | v1_relat_1(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ v1_relat_1(X22)
      | k1_relat_1(k2_xboole_0(X21,X22)) = k2_xboole_0(k1_relat_1(X21),k1_relat_1(X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & ~ r1_tarski(k6_subset_1(k1_relat_1(esk1_0),k1_relat_1(esk2_0)),k1_relat_1(k6_subset_1(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_18,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_25,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

fof(c_0_26,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k2_xboole_0(X13,X14)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_27,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,k2_xboole_0(X11,X12))
      | r1_tarski(k4_xboole_0(X10,X11),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_28,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(X1),k1_relat_1(esk2_0)) = k1_relat_1(k2_xboole_0(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(k4_xboole_0(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k4_xboole_0(esk1_0,X1))) = k1_relat_1(k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_30])).

fof(c_0_35,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X9,X8)) = k2_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k1_relat_1(esk2_0)),k1_relat_1(k4_xboole_0(esk1_0,X2)))
    | ~ r1_tarski(X1,k1_relat_1(k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk2_0),k1_relat_1(esk1_0)) = k1_relat_1(k2_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_30]),c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(esk1_0),k1_relat_1(esk2_0)),k1_relat_1(k6_subset_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k1_relat_1(esk2_0)),k1_relat_1(k4_xboole_0(esk1_0,esk2_0)))
    | ~ r1_tarski(X1,k1_relat_1(k2_xboole_0(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk1_0),k1_relat_1(k2_xboole_0(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0)),k1_relat_1(k4_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_15]),c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.77/0.99  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.77/0.99  # and selection function SelectDiffNegLit.
% 0.77/0.99  #
% 0.77/0.99  # Preprocessing time       : 0.026 s
% 0.77/0.99  # Presaturation interreduction done
% 0.77/0.99  
% 0.77/0.99  # Proof found!
% 0.77/0.99  # SZS status Theorem
% 0.77/0.99  # SZS output start CNFRefutation
% 0.77/0.99  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 0.77/0.99  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.77/0.99  fof(t15_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 0.77/0.99  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.77/0.99  fof(t13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relat_1)).
% 0.77/0.99  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.77/0.99  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 0.77/0.99  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.77/0.99  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.77/0.99  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.77/0.99  fof(c_0_10, plain, ![X15, X16]:m1_subset_1(k6_subset_1(X15,X16),k1_zfmisc_1(X15)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 0.77/0.99  fof(c_0_11, plain, ![X17, X18]:k6_subset_1(X17,X18)=k4_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.77/0.99  fof(c_0_12, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t15_relat_1])).
% 0.77/0.99  fof(c_0_13, plain, ![X19, X20]:(~v1_relat_1(X19)|(~m1_subset_1(X20,k1_zfmisc_1(X19))|v1_relat_1(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.77/0.99  cnf(c_0_14, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.77/0.99  cnf(c_0_15, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.77/0.99  fof(c_0_16, plain, ![X21, X22]:(~v1_relat_1(X21)|(~v1_relat_1(X22)|k1_relat_1(k2_xboole_0(X21,X22))=k2_xboole_0(k1_relat_1(X21),k1_relat_1(X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).
% 0.77/0.99  fof(c_0_17, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&~r1_tarski(k6_subset_1(k1_relat_1(esk1_0),k1_relat_1(esk2_0)),k1_relat_1(k6_subset_1(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.77/0.99  cnf(c_0_18, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.77/0.99  cnf(c_0_19, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.77/0.99  cnf(c_0_20, plain, (k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.77/0.99  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.77/0.99  cnf(c_0_22, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.77/0.99  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.77/0.99  fof(c_0_24, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.77/0.99  fof(c_0_25, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 0.77/0.99  fof(c_0_26, plain, ![X13, X14]:k4_xboole_0(X13,k2_xboole_0(X13,X14))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.77/0.99  fof(c_0_27, plain, ![X10, X11, X12]:(~r1_tarski(X10,k2_xboole_0(X11,X12))|r1_tarski(k4_xboole_0(X10,X11),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.77/0.99  cnf(c_0_28, negated_conjecture, (k2_xboole_0(k1_relat_1(X1),k1_relat_1(esk2_0))=k1_relat_1(k2_xboole_0(X1,esk2_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.77/0.99  cnf(c_0_29, negated_conjecture, (v1_relat_1(k4_xboole_0(esk1_0,X1))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.77/0.99  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.77/0.99  cnf(c_0_31, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.77/0.99  cnf(c_0_32, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.77/0.99  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.77/0.99  cnf(c_0_34, negated_conjecture, (k2_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k4_xboole_0(esk1_0,X1)))=k1_relat_1(k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_30])).
% 0.77/0.99  fof(c_0_35, plain, ![X8, X9]:k2_xboole_0(X8,k4_xboole_0(X9,X8))=k2_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.77/0.99  cnf(c_0_36, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.77/0.99  cnf(c_0_37, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k1_relat_1(esk2_0)),k1_relat_1(k4_xboole_0(esk1_0,X2)))|~r1_tarski(X1,k1_relat_1(k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,X2))))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.77/0.99  cnf(c_0_38, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.77/0.99  cnf(c_0_39, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_36, c_0_30])).
% 0.77/0.99  cnf(c_0_40, negated_conjecture, (k2_xboole_0(k1_relat_1(esk2_0),k1_relat_1(esk1_0))=k1_relat_1(k2_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_23]), c_0_30]), c_0_30])).
% 0.77/0.99  cnf(c_0_41, negated_conjecture, (~r1_tarski(k6_subset_1(k1_relat_1(esk1_0),k1_relat_1(esk2_0)),k1_relat_1(k6_subset_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.77/0.99  cnf(c_0_42, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k1_relat_1(esk2_0)),k1_relat_1(k4_xboole_0(esk1_0,esk2_0)))|~r1_tarski(X1,k1_relat_1(k2_xboole_0(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.77/0.99  cnf(c_0_43, negated_conjecture, (r1_tarski(k1_relat_1(esk1_0),k1_relat_1(k2_xboole_0(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.77/0.99  cnf(c_0_44, negated_conjecture, (~r1_tarski(k4_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0)),k1_relat_1(k4_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_15]), c_0_15])).
% 0.77/0.99  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), ['proof']).
% 0.77/0.99  # SZS output end CNFRefutation
% 0.77/0.99  # Proof object total steps             : 46
% 0.77/0.99  # Proof object clause steps            : 25
% 0.77/0.99  # Proof object formula steps           : 21
% 0.77/0.99  # Proof object conjectures             : 15
% 0.77/0.99  # Proof object clause conjectures      : 12
% 0.77/0.99  # Proof object formula conjectures     : 3
% 0.77/0.99  # Proof object initial clauses used    : 12
% 0.77/0.99  # Proof object initial formulas used   : 10
% 0.77/0.99  # Proof object generating inferences   : 11
% 0.77/0.99  # Proof object simplifying inferences  : 8
% 0.77/0.99  # Training examples: 0 positive, 0 negative
% 0.77/0.99  # Parsed axioms                        : 10
% 0.77/0.99  # Removed by relevancy pruning/SinE    : 0
% 0.77/0.99  # Initial clauses                      : 13
% 0.77/0.99  # Removed in clause preprocessing      : 1
% 0.77/0.99  # Initial clauses in saturation        : 12
% 0.77/0.99  # Processed clauses                    : 3313
% 0.77/0.99  # ...of these trivial                  : 532
% 0.77/0.99  # ...subsumed                          : 1031
% 0.77/0.99  # ...remaining for further processing  : 1750
% 0.77/0.99  # Other redundant clauses eliminated   : 0
% 0.77/0.99  # Clauses deleted for lack of memory   : 0
% 0.77/0.99  # Backward-subsumed                    : 5
% 0.77/0.99  # Backward-rewritten                   : 118
% 0.77/0.99  # Generated clauses                    : 90225
% 0.77/0.99  # ...of the previous two non-trivial   : 36548
% 0.77/0.99  # Contextual simplify-reflections      : 0
% 0.77/0.99  # Paramodulations                      : 90225
% 0.77/0.99  # Factorizations                       : 0
% 0.77/0.99  # Equation resolutions                 : 0
% 0.77/0.99  # Propositional unsat checks           : 0
% 0.77/0.99  #    Propositional check models        : 0
% 0.77/0.99  #    Propositional check unsatisfiable : 0
% 0.77/0.99  #    Propositional clauses             : 0
% 0.77/0.99  #    Propositional clauses after purity: 0
% 0.77/0.99  #    Propositional unsat core size     : 0
% 0.77/0.99  #    Propositional preprocessing time  : 0.000
% 0.77/0.99  #    Propositional encoding time       : 0.000
% 0.77/0.99  #    Propositional solver time         : 0.000
% 0.77/0.99  #    Success case prop preproc time    : 0.000
% 0.77/0.99  #    Success case prop encoding time   : 0.000
% 0.77/0.99  #    Success case prop solver time     : 0.000
% 0.77/0.99  # Current number of processed clauses  : 1615
% 0.77/0.99  #    Positive orientable unit clauses  : 1455
% 0.77/0.99  #    Positive unorientable unit clauses: 8
% 0.77/0.99  #    Negative unit clauses             : 1
% 0.77/0.99  #    Non-unit-clauses                  : 151
% 0.77/0.99  # Current number of unprocessed clauses: 33191
% 0.77/0.99  # ...number of literals in the above   : 36763
% 0.77/0.99  # Current number of archived formulas  : 0
% 0.77/0.99  # Current number of archived clauses   : 136
% 0.77/0.99  # Clause-clause subsumption calls (NU) : 16851
% 0.77/0.99  # Rec. Clause-clause subsumption calls : 16477
% 0.77/0.99  # Non-unit clause-clause subsumptions  : 994
% 0.77/0.99  # Unit Clause-clause subsumption calls : 820
% 0.77/0.99  # Rewrite failures with RHS unbound    : 0
% 0.77/0.99  # BW rewrite match attempts            : 35213
% 0.77/0.99  # BW rewrite match successes           : 134
% 0.77/0.99  # Condensation attempts                : 0
% 0.77/0.99  # Condensation successes               : 0
% 0.77/0.99  # Termbank termtop insertions          : 1503303
% 0.77/0.99  
% 0.77/0.99  # -------------------------------------------------
% 0.77/0.99  # User time                : 0.617 s
% 0.77/0.99  # System time              : 0.033 s
% 0.77/0.99  # Total time               : 0.650 s
% 0.77/0.99  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
