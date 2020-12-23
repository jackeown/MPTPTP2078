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
% DateTime   : Thu Dec  3 10:48:19 EST 2020

% Result     : Theorem 1.45s
% Output     : CNFRefutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 174 expanded)
%              Number of clauses        :   38 (  79 expanded)
%              Number of leaves         :   12 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 287 expanded)
%              Number of equality atoms :   19 (  80 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t26_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(t28_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc3_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(c_0_12,plain,(
    ! [X9,X10] : r1_tarski(X9,k2_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_13,plain,(
    ! [X13,X14] : k3_tarski(k2_tarski(X13,X14)) = k2_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,k2_xboole_0(X7,X8))
      | r1_tarski(k4_xboole_0(X6,X7),X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X11,X12] : k2_tarski(X11,X12) = k2_tarski(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_18,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_22,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_24,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ v1_relat_1(X26)
      | k2_relat_1(k2_xboole_0(X25,X26)) = k2_xboole_0(k2_relat_1(X25),k2_relat_1(X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t28_relat_1])).

fof(c_0_26,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | v1_relat_1(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_29,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ v1_relat_1(X22)
      | v1_relat_1(k2_xboole_0(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_relat_1])])).

cnf(c_0_30,plain,
    ( k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & ~ r1_tarski(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_32,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( v1_relat_1(k2_xboole_0(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(X1,X2))) = k3_tarski(k2_tarski(k2_relat_1(X1),k2_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_16]),c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_39,plain,(
    ! [X23,X24] :
      ( ( r1_tarski(k1_relat_1(X23),k1_relat_1(X24))
        | ~ r1_tarski(X23,X24)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) )
      & ( r1_tarski(k2_relat_1(X23),k2_relat_1(X24))
        | ~ r1_tarski(X23,X24)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_19])).

cnf(c_0_41,plain,
    ( v1_relat_1(k3_tarski(k2_tarski(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_34,c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( k3_tarski(k2_tarski(k2_relat_1(X1),k2_relat_1(esk2_0))) = k2_relat_1(k3_tarski(k2_tarski(X1,esk2_0)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(k4_xboole_0(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_44,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X5,X4)) = k2_xboole_0(X4,X5) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_45,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(k3_tarski(k2_tarski(X1,esk1_0)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(k4_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( k3_tarski(k2_tarski(k2_relat_1(esk2_0),k2_relat_1(k4_xboole_0(esk1_0,X1)))) = k2_relat_1(k3_tarski(k2_tarski(esk2_0,k4_xboole_0(esk1_0,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_20]),c_0_20])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(k3_tarski(k2_tarski(X1,X2))))
    | ~ v1_relat_1(k3_tarski(k2_tarski(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_19]),c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(k3_tarski(k2_tarski(esk1_0,k4_xboole_0(esk2_0,X1)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_20])).

fof(c_0_53,plain,(
    ! [X15,X16] : k6_subset_1(X15,X16) = k4_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,X2)))
    | ~ r1_tarski(X1,k2_relat_1(k3_tarski(k2_tarski(esk2_0,k4_xboole_0(esk1_0,X2))))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_49])).

cnf(c_0_55,plain,
    ( k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1))) = k3_tarski(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_16]),c_0_16])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k3_tarski(k2_tarski(esk1_0,k4_xboole_0(esk2_0,X1))))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_58,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,esk2_0)))
    | ~ r1_tarski(X1,k2_relat_1(k3_tarski(k2_tarski(esk2_0,esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k3_tarski(k2_tarski(esk2_0,esk1_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_55]),c_0_20])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58]),c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.45/1.69  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 1.45/1.69  # and selection function SelectDiffNegLit.
% 1.45/1.69  #
% 1.45/1.69  # Preprocessing time       : 0.027 s
% 1.45/1.69  # Presaturation interreduction done
% 1.45/1.69  
% 1.45/1.69  # Proof found!
% 1.45/1.69  # SZS status Theorem
% 1.45/1.69  # SZS output start CNFRefutation
% 1.45/1.69  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.45/1.69  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.45/1.69  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.45/1.69  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.45/1.69  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.45/1.69  fof(t26_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_relat_1)).
% 1.45/1.69  fof(t28_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 1.45/1.69  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.45/1.69  fof(fc3_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k2_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_relat_1)).
% 1.45/1.69  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 1.45/1.69  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.45/1.69  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.45/1.69  fof(c_0_12, plain, ![X9, X10]:r1_tarski(X9,k2_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 1.45/1.69  fof(c_0_13, plain, ![X13, X14]:k3_tarski(k2_tarski(X13,X14))=k2_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.45/1.69  fof(c_0_14, plain, ![X6, X7, X8]:(~r1_tarski(X6,k2_xboole_0(X7,X8))|r1_tarski(k4_xboole_0(X6,X7),X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 1.45/1.69  cnf(c_0_15, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.45/1.69  cnf(c_0_16, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.45/1.69  fof(c_0_17, plain, ![X11, X12]:k2_tarski(X11,X12)=k2_tarski(X12,X11), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.45/1.69  cnf(c_0_18, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.45/1.69  cnf(c_0_19, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 1.45/1.69  cnf(c_0_20, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.45/1.69  fof(c_0_21, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.45/1.69  cnf(c_0_22, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_18, c_0_16])).
% 1.45/1.69  cnf(c_0_23, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 1.45/1.69  fof(c_0_24, plain, ![X25, X26]:(~v1_relat_1(X25)|(~v1_relat_1(X26)|k2_relat_1(k2_xboole_0(X25,X26))=k2_xboole_0(k2_relat_1(X25),k2_relat_1(X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).
% 1.45/1.69  fof(c_0_25, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t28_relat_1])).
% 1.45/1.69  fof(c_0_26, plain, ![X19, X20]:(~v1_relat_1(X19)|(~m1_subset_1(X20,k1_zfmisc_1(X19))|v1_relat_1(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 1.45/1.69  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.45/1.69  cnf(c_0_28, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.45/1.69  fof(c_0_29, plain, ![X21, X22]:(~v1_relat_1(X21)|~v1_relat_1(X22)|v1_relat_1(k2_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_relat_1])])).
% 1.45/1.69  cnf(c_0_30, plain, (k2_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.45/1.69  fof(c_0_31, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&~r1_tarski(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 1.45/1.69  cnf(c_0_32, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.45/1.69  cnf(c_0_33, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.45/1.69  cnf(c_0_34, plain, (v1_relat_1(k2_xboole_0(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.45/1.69  cnf(c_0_35, plain, (k2_relat_1(k3_tarski(k2_tarski(X1,X2)))=k3_tarski(k2_tarski(k2_relat_1(X1),k2_relat_1(X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_16]), c_0_16])).
% 1.45/1.69  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.45/1.69  cnf(c_0_37, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.45/1.69  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.45/1.69  fof(c_0_39, plain, ![X23, X24]:((r1_tarski(k1_relat_1(X23),k1_relat_1(X24))|~r1_tarski(X23,X24)|~v1_relat_1(X24)|~v1_relat_1(X23))&(r1_tarski(k2_relat_1(X23),k2_relat_1(X24))|~r1_tarski(X23,X24)|~v1_relat_1(X24)|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 1.45/1.69  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_27, c_0_19])).
% 1.45/1.69  cnf(c_0_41, plain, (v1_relat_1(k3_tarski(k2_tarski(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_34, c_0_16])).
% 1.45/1.69  cnf(c_0_42, negated_conjecture, (k3_tarski(k2_tarski(k2_relat_1(X1),k2_relat_1(esk2_0)))=k2_relat_1(k3_tarski(k2_tarski(X1,esk2_0)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.45/1.69  cnf(c_0_43, negated_conjecture, (v1_relat_1(k4_xboole_0(esk1_0,X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.45/1.69  fof(c_0_44, plain, ![X4, X5]:k2_xboole_0(X4,k4_xboole_0(X5,X4))=k2_xboole_0(X4,X5), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 1.45/1.69  cnf(c_0_45, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.45/1.69  cnf(c_0_46, plain, (v1_relat_1(X1)|~v1_relat_1(k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_32, c_0_40])).
% 1.45/1.69  cnf(c_0_47, negated_conjecture, (v1_relat_1(k3_tarski(k2_tarski(X1,esk1_0)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_38])).
% 1.45/1.69  cnf(c_0_48, negated_conjecture, (v1_relat_1(k4_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 1.45/1.69  cnf(c_0_49, negated_conjecture, (k3_tarski(k2_tarski(k2_relat_1(esk2_0),k2_relat_1(k4_xboole_0(esk1_0,X1))))=k2_relat_1(k3_tarski(k2_tarski(esk2_0,k4_xboole_0(esk1_0,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_20]), c_0_20])).
% 1.45/1.69  cnf(c_0_50, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.45/1.69  cnf(c_0_51, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(k3_tarski(k2_tarski(X1,X2))))|~v1_relat_1(k3_tarski(k2_tarski(X1,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_19]), c_0_46])).
% 1.45/1.69  cnf(c_0_52, negated_conjecture, (v1_relat_1(k3_tarski(k2_tarski(esk1_0,k4_xboole_0(esk2_0,X1))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_20])).
% 1.45/1.69  fof(c_0_53, plain, ![X15, X16]:k6_subset_1(X15,X16)=k4_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 1.45/1.69  cnf(c_0_54, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,X2)))|~r1_tarski(X1,k2_relat_1(k3_tarski(k2_tarski(esk2_0,k4_xboole_0(esk1_0,X2)))))), inference(spm,[status(thm)],[c_0_22, c_0_49])).
% 1.45/1.69  cnf(c_0_55, plain, (k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1)))=k3_tarski(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_16]), c_0_16])).
% 1.45/1.69  cnf(c_0_56, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k3_tarski(k2_tarski(esk1_0,k4_xboole_0(esk2_0,X1)))))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 1.45/1.69  cnf(c_0_57, negated_conjecture, (~r1_tarski(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.45/1.69  cnf(c_0_58, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.45/1.69  cnf(c_0_59, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,esk2_0)))|~r1_tarski(X1,k2_relat_1(k3_tarski(k2_tarski(esk2_0,esk1_0))))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 1.45/1.69  cnf(c_0_60, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k3_tarski(k2_tarski(esk2_0,esk1_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_55]), c_0_20])).
% 1.45/1.69  cnf(c_0_61, negated_conjecture, (~r1_tarski(k4_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58]), c_0_58])).
% 1.45/1.69  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), ['proof']).
% 1.45/1.69  # SZS output end CNFRefutation
% 1.45/1.69  # Proof object total steps             : 63
% 1.45/1.69  # Proof object clause steps            : 38
% 1.45/1.69  # Proof object formula steps           : 25
% 1.45/1.69  # Proof object conjectures             : 18
% 1.45/1.69  # Proof object clause conjectures      : 15
% 1.45/1.69  # Proof object formula conjectures     : 3
% 1.45/1.69  # Proof object initial clauses used    : 14
% 1.45/1.69  # Proof object initial formulas used   : 12
% 1.45/1.69  # Proof object generating inferences   : 18
% 1.45/1.69  # Proof object simplifying inferences  : 15
% 1.45/1.69  # Training examples: 0 positive, 0 negative
% 1.45/1.69  # Parsed axioms                        : 12
% 1.45/1.69  # Removed by relevancy pruning/SinE    : 0
% 1.45/1.69  # Initial clauses                      : 16
% 1.45/1.69  # Removed in clause preprocessing      : 2
% 1.45/1.69  # Initial clauses in saturation        : 14
% 1.45/1.69  # Processed clauses                    : 2539
% 1.45/1.69  # ...of these trivial                  : 144
% 1.45/1.69  # ...subsumed                          : 323
% 1.45/1.69  # ...remaining for further processing  : 2072
% 1.45/1.69  # Other redundant clauses eliminated   : 0
% 1.45/1.69  # Clauses deleted for lack of memory   : 0
% 1.45/1.69  # Backward-subsumed                    : 32
% 1.45/1.69  # Backward-rewritten                   : 110
% 1.45/1.69  # Generated clauses                    : 186244
% 1.45/1.69  # ...of the previous two non-trivial   : 180741
% 1.45/1.69  # Contextual simplify-reflections      : 86
% 1.45/1.69  # Paramodulations                      : 186244
% 1.45/1.69  # Factorizations                       : 0
% 1.45/1.69  # Equation resolutions                 : 0
% 1.45/1.69  # Propositional unsat checks           : 0
% 1.45/1.69  #    Propositional check models        : 0
% 1.45/1.69  #    Propositional check unsatisfiable : 0
% 1.45/1.69  #    Propositional clauses             : 0
% 1.45/1.69  #    Propositional clauses after purity: 0
% 1.45/1.69  #    Propositional unsat core size     : 0
% 1.45/1.69  #    Propositional preprocessing time  : 0.000
% 1.45/1.69  #    Propositional encoding time       : 0.000
% 1.45/1.69  #    Propositional solver time         : 0.000
% 1.45/1.69  #    Success case prop preproc time    : 0.000
% 1.45/1.69  #    Success case prop encoding time   : 0.000
% 1.45/1.69  #    Success case prop solver time     : 0.000
% 1.45/1.69  # Current number of processed clauses  : 1916
% 1.45/1.69  #    Positive orientable unit clauses  : 986
% 1.45/1.69  #    Positive unorientable unit clauses: 1
% 1.45/1.69  #    Negative unit clauses             : 1
% 1.45/1.69  #    Non-unit-clauses                  : 928
% 1.45/1.69  # Current number of unprocessed clauses: 178126
% 1.45/1.69  # ...number of literals in the above   : 181931
% 1.45/1.69  # Current number of archived formulas  : 0
% 1.45/1.69  # Current number of archived clauses   : 158
% 1.45/1.69  # Clause-clause subsumption calls (NU) : 113280
% 1.45/1.69  # Rec. Clause-clause subsumption calls : 109316
% 1.45/1.69  # Non-unit clause-clause subsumptions  : 441
% 1.45/1.69  # Unit Clause-clause subsumption calls : 36267
% 1.45/1.69  # Rewrite failures with RHS unbound    : 0
% 1.45/1.69  # BW rewrite match attempts            : 78721
% 1.45/1.69  # BW rewrite match successes           : 101
% 1.45/1.69  # Condensation attempts                : 0
% 1.45/1.69  # Condensation successes               : 0
% 1.45/1.69  # Termbank termtop insertions          : 4037604
% 1.45/1.70  
% 1.45/1.70  # -------------------------------------------------
% 1.45/1.70  # User time                : 1.256 s
% 1.45/1.70  # System time              : 0.099 s
% 1.45/1.70  # Total time               : 1.355 s
% 1.45/1.70  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
