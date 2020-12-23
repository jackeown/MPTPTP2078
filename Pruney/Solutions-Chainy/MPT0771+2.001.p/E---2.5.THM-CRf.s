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
% DateTime   : Thu Dec  3 10:56:45 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 100 expanded)
%              Number of clauses        :   35 (  43 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  130 ( 212 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t20_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))
        & r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t31_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(t18_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,X1) = k8_relat_1(X1,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

fof(t116_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

fof(t17_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,X1) = k7_relat_1(k8_relat_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(c_0_15,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_16,plain,(
    ! [X4,X5] : r1_tarski(k3_xboole_0(X4,X5),X4) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))
          & r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_wellord1])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_relat_1(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | ~ r1_tarski(X20,X21)
      | r1_tarski(k3_relat_1(X20),k3_relat_1(X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ( ~ r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0))
      | ~ r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_23,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_25,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | k2_wellord1(X31,X30) = k8_relat_1(X30,k7_relat_1(X31,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_wellord1])])).

fof(c_0_26,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | v1_relat_1(k7_relat_1(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_30,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | k2_wellord1(X24,X25) = k3_xboole_0(X24,k2_zfmisc_1(X25,X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

fof(c_0_31,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | r1_tarski(k2_relat_1(k8_relat_1(X18,X19)),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).

cnf(c_0_32,plain,
    ( k2_wellord1(X1,X2) = k8_relat_1(X2,k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | k2_wellord1(X29,X28) = k7_relat_1(k8_relat_1(X28,X29),X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_wellord1])])).

fof(c_0_35,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | v1_relat_1(k8_relat_1(X16,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

fof(c_0_36,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | v1_relat_1(k2_wellord1(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(esk2_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(k3_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_39,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_40,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X8,X7)
      | r1_tarski(k2_xboole_0(X6,X8),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_41,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( k8_relat_1(X1,k7_relat_1(esk2_0,X1)) = k2_wellord1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

fof(c_0_44,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | r1_tarski(k1_relat_1(k7_relat_1(X23,X22)),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_45,plain,
    ( k2_wellord1(X1,X2) = k7_relat_1(k8_relat_1(X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_47,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | k3_relat_1(X13) = k2_xboole_0(k1_relat_1(X13),k2_relat_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_48,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,X1)),k3_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_20]),c_0_38])])).

cnf(c_0_50,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_zfmisc_1(X1,X1)) = k2_wellord1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_28])).

cnf(c_0_51,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_wellord1(esk2_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( k7_relat_1(k8_relat_1(X1,esk2_0),X1) = k2_wellord1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_28])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_28])).

cnf(c_0_56,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(k2_wellord1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_28])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0))
    | ~ r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k3_relat_1(k2_wellord1(esk2_0,X1)),k3_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,k2_relat_1(k2_wellord1(esk2_0,X2))),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_wellord1(esk2_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_62,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(k2_wellord1(esk2_0,X1)),k2_relat_1(k2_wellord1(esk2_0,X1))) = k3_relat_1(k2_wellord1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k3_relat_1(k2_wellord1(esk2_0,X1)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:48:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S047N
% 0.21/0.45  # and selection function PSelectComplexPreferNEQ.
% 0.21/0.45  #
% 0.21/0.45  # Preprocessing time       : 0.027 s
% 0.21/0.45  # Presaturation interreduction done
% 0.21/0.45  
% 0.21/0.45  # Proof found!
% 0.21/0.45  # SZS status Theorem
% 0.21/0.45  # SZS output start CNFRefutation
% 0.21/0.45  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.45  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.21/0.45  fof(t20_wellord1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))&r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_wellord1)).
% 0.21/0.45  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.45  fof(t31_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 0.21/0.45  fof(t18_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_wellord1(X2,X1)=k8_relat_1(X1,k7_relat_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_wellord1)).
% 0.21/0.45  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.21/0.45  fof(d6_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k2_wellord1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 0.21/0.45  fof(t116_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 0.21/0.45  fof(t17_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_wellord1(X2,X1)=k7_relat_1(k8_relat_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_wellord1)).
% 0.21/0.45  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.21/0.45  fof(dt_k2_wellord1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k2_wellord1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 0.21/0.45  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.21/0.45  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 0.21/0.45  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 0.21/0.45  fof(c_0_15, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.45  fof(c_0_16, plain, ![X4, X5]:r1_tarski(k3_xboole_0(X4,X5),X4), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.21/0.45  fof(c_0_17, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))&r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1)))), inference(assume_negation,[status(cth)],[t20_wellord1])).
% 0.21/0.45  fof(c_0_18, plain, ![X11, X12]:(~v1_relat_1(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_relat_1(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.45  cnf(c_0_19, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.45  cnf(c_0_20, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.45  fof(c_0_21, plain, ![X20, X21]:(~v1_relat_1(X20)|(~v1_relat_1(X21)|(~r1_tarski(X20,X21)|r1_tarski(k3_relat_1(X20),k3_relat_1(X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).
% 0.21/0.45  fof(c_0_22, negated_conjecture, (v1_relat_1(esk2_0)&(~r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0))|~r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.21/0.45  cnf(c_0_23, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.45  cnf(c_0_24, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.45  fof(c_0_25, plain, ![X30, X31]:(~v1_relat_1(X31)|k2_wellord1(X31,X30)=k8_relat_1(X30,k7_relat_1(X31,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_wellord1])])).
% 0.21/0.45  fof(c_0_26, plain, ![X14, X15]:(~v1_relat_1(X14)|v1_relat_1(k7_relat_1(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.21/0.45  cnf(c_0_27, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.45  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.45  cnf(c_0_29, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.45  fof(c_0_30, plain, ![X24, X25]:(~v1_relat_1(X24)|k2_wellord1(X24,X25)=k3_xboole_0(X24,k2_zfmisc_1(X25,X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).
% 0.21/0.45  fof(c_0_31, plain, ![X18, X19]:(~v1_relat_1(X19)|r1_tarski(k2_relat_1(k8_relat_1(X18,X19)),X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).
% 0.21/0.45  cnf(c_0_32, plain, (k2_wellord1(X1,X2)=k8_relat_1(X2,k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.45  cnf(c_0_33, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.45  fof(c_0_34, plain, ![X28, X29]:(~v1_relat_1(X29)|k2_wellord1(X29,X28)=k7_relat_1(k8_relat_1(X28,X29),X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_wellord1])])).
% 0.21/0.45  fof(c_0_35, plain, ![X16, X17]:(~v1_relat_1(X17)|v1_relat_1(k8_relat_1(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.21/0.45  fof(c_0_36, plain, ![X26, X27]:(~v1_relat_1(X26)|v1_relat_1(k2_wellord1(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).
% 0.21/0.45  cnf(c_0_37, negated_conjecture, (r1_tarski(k3_relat_1(X1),k3_relat_1(esk2_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.45  cnf(c_0_38, negated_conjecture, (v1_relat_1(k3_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.21/0.45  cnf(c_0_39, plain, (k2_wellord1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.45  fof(c_0_40, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X8,X7)|r1_tarski(k2_xboole_0(X6,X8),X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.21/0.45  cnf(c_0_41, plain, (r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.45  cnf(c_0_42, negated_conjecture, (k8_relat_1(X1,k7_relat_1(esk2_0,X1))=k2_wellord1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_28])).
% 0.21/0.45  cnf(c_0_43, negated_conjecture, (v1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_33, c_0_28])).
% 0.21/0.45  fof(c_0_44, plain, ![X22, X23]:(~v1_relat_1(X23)|r1_tarski(k1_relat_1(k7_relat_1(X23,X22)),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.21/0.45  cnf(c_0_45, plain, (k2_wellord1(X1,X2)=k7_relat_1(k8_relat_1(X2,X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.45  cnf(c_0_46, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.45  fof(c_0_47, plain, ![X13]:(~v1_relat_1(X13)|k3_relat_1(X13)=k2_xboole_0(k1_relat_1(X13),k2_relat_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.21/0.45  cnf(c_0_48, plain, (v1_relat_1(k2_wellord1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.45  cnf(c_0_49, negated_conjecture, (r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,X1)),k3_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_20]), c_0_38])])).
% 0.21/0.45  cnf(c_0_50, negated_conjecture, (k3_xboole_0(esk2_0,k2_zfmisc_1(X1,X1))=k2_wellord1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_28])).
% 0.21/0.45  cnf(c_0_51, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.45  cnf(c_0_52, negated_conjecture, (r1_tarski(k2_relat_1(k2_wellord1(esk2_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.21/0.45  cnf(c_0_53, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.45  cnf(c_0_54, negated_conjecture, (k7_relat_1(k8_relat_1(X1,esk2_0),X1)=k2_wellord1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_45, c_0_28])).
% 0.21/0.45  cnf(c_0_55, negated_conjecture, (v1_relat_1(k8_relat_1(X1,esk2_0))), inference(spm,[status(thm)],[c_0_46, c_0_28])).
% 0.21/0.45  cnf(c_0_56, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.45  cnf(c_0_57, negated_conjecture, (v1_relat_1(k2_wellord1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_48, c_0_28])).
% 0.21/0.45  cnf(c_0_58, negated_conjecture, (~r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0))|~r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.45  cnf(c_0_59, negated_conjecture, (r1_tarski(k3_relat_1(k2_wellord1(esk2_0,X1)),k3_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.45  cnf(c_0_60, negated_conjecture, (r1_tarski(k2_xboole_0(X1,k2_relat_1(k2_wellord1(esk2_0,X2))),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.45  cnf(c_0_61, negated_conjecture, (r1_tarski(k1_relat_1(k2_wellord1(esk2_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.21/0.45  cnf(c_0_62, negated_conjecture, (k2_xboole_0(k1_relat_1(k2_wellord1(esk2_0,X1)),k2_relat_1(k2_wellord1(esk2_0,X1)))=k3_relat_1(k2_wellord1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.45  cnf(c_0_63, negated_conjecture, (~r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])])).
% 0.21/0.45  cnf(c_0_64, negated_conjecture, (r1_tarski(k3_relat_1(k2_wellord1(esk2_0,X1)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.21/0.45  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64])]), ['proof']).
% 0.21/0.45  # SZS output end CNFRefutation
% 0.21/0.45  # Proof object total steps             : 66
% 0.21/0.45  # Proof object clause steps            : 35
% 0.21/0.45  # Proof object formula steps           : 31
% 0.21/0.45  # Proof object conjectures             : 22
% 0.21/0.45  # Proof object clause conjectures      : 19
% 0.21/0.45  # Proof object formula conjectures     : 3
% 0.21/0.45  # Proof object initial clauses used    : 16
% 0.21/0.45  # Proof object initial formulas used   : 15
% 0.21/0.45  # Proof object generating inferences   : 17
% 0.21/0.45  # Proof object simplifying inferences  : 11
% 0.21/0.45  # Training examples: 0 positive, 0 negative
% 0.21/0.45  # Parsed axioms                        : 15
% 0.21/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.45  # Initial clauses                      : 17
% 0.21/0.45  # Removed in clause preprocessing      : 0
% 0.21/0.45  # Initial clauses in saturation        : 17
% 0.21/0.45  # Processed clauses                    : 416
% 0.21/0.45  # ...of these trivial                  : 8
% 0.21/0.45  # ...subsumed                          : 8
% 0.21/0.45  # ...remaining for further processing  : 400
% 0.21/0.45  # Other redundant clauses eliminated   : 0
% 0.21/0.45  # Clauses deleted for lack of memory   : 0
% 0.21/0.45  # Backward-subsumed                    : 0
% 0.21/0.45  # Backward-rewritten                   : 5
% 0.21/0.45  # Generated clauses                    : 6802
% 0.21/0.45  # ...of the previous two non-trivial   : 6679
% 0.21/0.45  # Contextual simplify-reflections      : 0
% 0.21/0.45  # Paramodulations                      : 6802
% 0.21/0.45  # Factorizations                       : 0
% 0.21/0.45  # Equation resolutions                 : 0
% 0.21/0.45  # Propositional unsat checks           : 0
% 0.21/0.45  #    Propositional check models        : 0
% 0.21/0.45  #    Propositional check unsatisfiable : 0
% 0.21/0.45  #    Propositional clauses             : 0
% 0.21/0.45  #    Propositional clauses after purity: 0
% 0.21/0.45  #    Propositional unsat core size     : 0
% 0.21/0.45  #    Propositional preprocessing time  : 0.000
% 0.21/0.45  #    Propositional encoding time       : 0.000
% 0.21/0.45  #    Propositional solver time         : 0.000
% 0.21/0.45  #    Success case prop preproc time    : 0.000
% 0.21/0.45  #    Success case prop encoding time   : 0.000
% 0.21/0.45  #    Success case prop solver time     : 0.000
% 0.21/0.45  # Current number of processed clauses  : 378
% 0.21/0.45  #    Positive orientable unit clauses  : 326
% 0.21/0.45  #    Positive unorientable unit clauses: 0
% 0.21/0.45  #    Negative unit clauses             : 0
% 0.21/0.45  #    Non-unit-clauses                  : 52
% 0.21/0.45  # Current number of unprocessed clauses: 6297
% 0.21/0.45  # ...number of literals in the above   : 7025
% 0.21/0.45  # Current number of archived formulas  : 0
% 0.21/0.45  # Current number of archived clauses   : 22
% 0.21/0.45  # Clause-clause subsumption calls (NU) : 249
% 0.21/0.45  # Rec. Clause-clause subsumption calls : 241
% 0.21/0.45  # Non-unit clause-clause subsumptions  : 8
% 0.21/0.45  # Unit Clause-clause subsumption calls : 59
% 0.21/0.45  # Rewrite failures with RHS unbound    : 0
% 0.21/0.45  # BW rewrite match attempts            : 1797
% 0.21/0.45  # BW rewrite match successes           : 5
% 0.21/0.45  # Condensation attempts                : 0
% 0.21/0.45  # Condensation successes               : 0
% 0.21/0.45  # Termbank termtop insertions          : 101442
% 0.21/0.46  
% 0.21/0.46  # -------------------------------------------------
% 0.21/0.46  # User time                : 0.101 s
% 0.21/0.46  # System time              : 0.007 s
% 0.21/0.46  # Total time               : 0.107 s
% 0.21/0.46  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
