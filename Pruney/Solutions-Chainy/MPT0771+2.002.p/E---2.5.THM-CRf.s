%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:46 EST 2020

% Result     : Theorem 0.49s
% Output     : CNFRefutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 124 expanded)
%              Number of clauses        :   34 (  53 expanded)
%              Number of leaves         :   14 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  124 ( 263 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t20_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))
        & r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t31_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(t18_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,X1) = k8_relat_1(X1,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

fof(t116_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(t140_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k8_relat_1(X1,X3),X2) = k8_relat_1(X1,k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(c_0_14,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_15,plain,(
    ! [X4,X5] : r1_tarski(k3_xboole_0(X4,X5),X4) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))
          & r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_wellord1])).

fof(c_0_17,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_relat_1(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ v1_relat_1(X24)
      | ~ r1_tarski(X23,X24)
      | r1_tarski(k3_relat_1(X23),k3_relat_1(X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ( ~ r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0))
      | ~ r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_22,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | k2_wellord1(X30,X29) = k8_relat_1(X29,k7_relat_1(X30,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_wellord1])])).

fof(c_0_25,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | v1_relat_1(k7_relat_1(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_26,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X27)
      | k2_wellord1(X27,X28) = k3_xboole_0(X27,k2_zfmisc_1(X28,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

cnf(c_0_27,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_30,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | r1_tarski(k2_relat_1(k8_relat_1(X18,X19)),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).

cnf(c_0_31,plain,
    ( k2_wellord1(X1,X2) = k8_relat_1(X2,k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X20,X21,X22] :
      ( ~ v1_relat_1(X22)
      | k7_relat_1(k8_relat_1(X20,X22),X21) = k8_relat_1(X20,k7_relat_1(X22,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).

fof(c_0_35,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | v1_relat_1(k8_relat_1(X16,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(esk2_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(k3_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

fof(c_0_38,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X8,X7)
      | r1_tarski(k2_xboole_0(X6,X8),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( k8_relat_1(X1,k7_relat_1(esk2_0,X1)) = k2_wellord1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_28])).

fof(c_0_42,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | k3_relat_1(X13) = k2_xboole_0(k1_relat_1(X13),k2_relat_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_43,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_zfmisc_1(X1,X1)) = k2_wellord1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

fof(c_0_44,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | r1_tarski(k1_relat_1(k7_relat_1(X26,X25)),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_45,plain,
    ( k7_relat_1(k8_relat_1(X2,X1),X3) = k8_relat_1(X2,k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,X1)),k3_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_19]),c_0_37])])).

cnf(c_0_48,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_wellord1(esk2_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_50,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(k2_wellord1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_43]),c_0_28])])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( k7_relat_1(k8_relat_1(X1,esk2_0),X1) = k2_wellord1(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_28])])).

cnf(c_0_54,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_28])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0))
    | ~ r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k3_relat_1(k2_wellord1(esk2_0,X1)),k3_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,k2_relat_1(k2_wellord1(esk2_0,X2))),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(k2_wellord1(esk2_0,X1)),k2_relat_1(k2_wellord1(esk2_0,X1))) = k3_relat_1(k2_wellord1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_wellord1(esk2_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k3_relat_1(k2_wellord1(esk2_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.49/0.70  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S047N
% 0.49/0.70  # and selection function PSelectComplexPreferNEQ.
% 0.49/0.70  #
% 0.49/0.70  # Preprocessing time       : 0.041 s
% 0.49/0.70  # Presaturation interreduction done
% 0.49/0.70  
% 0.49/0.70  # Proof found!
% 0.49/0.70  # SZS status Theorem
% 0.49/0.70  # SZS output start CNFRefutation
% 0.49/0.70  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.49/0.70  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.49/0.70  fof(t20_wellord1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))&r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_wellord1)).
% 0.49/0.70  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.49/0.70  fof(t31_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 0.49/0.70  fof(t18_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_wellord1(X2,X1)=k8_relat_1(X1,k7_relat_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_wellord1)).
% 0.49/0.70  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.49/0.70  fof(d6_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k2_wellord1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_wellord1)).
% 0.49/0.70  fof(t116_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 0.49/0.70  fof(t140_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k8_relat_1(X1,X3),X2)=k8_relat_1(X1,k7_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 0.49/0.70  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.49/0.70  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.49/0.70  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 0.49/0.70  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.49/0.70  fof(c_0_14, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.49/0.70  fof(c_0_15, plain, ![X4, X5]:r1_tarski(k3_xboole_0(X4,X5),X4), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.49/0.70  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))&r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1)))), inference(assume_negation,[status(cth)],[t20_wellord1])).
% 0.49/0.70  fof(c_0_17, plain, ![X11, X12]:(~v1_relat_1(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_relat_1(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.49/0.70  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.49/0.70  cnf(c_0_19, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.49/0.70  fof(c_0_20, plain, ![X23, X24]:(~v1_relat_1(X23)|(~v1_relat_1(X24)|(~r1_tarski(X23,X24)|r1_tarski(k3_relat_1(X23),k3_relat_1(X24))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).
% 0.49/0.70  fof(c_0_21, negated_conjecture, (v1_relat_1(esk2_0)&(~r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0))|~r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.49/0.70  cnf(c_0_22, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.49/0.70  cnf(c_0_23, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.49/0.70  fof(c_0_24, plain, ![X29, X30]:(~v1_relat_1(X30)|k2_wellord1(X30,X29)=k8_relat_1(X29,k7_relat_1(X30,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_wellord1])])).
% 0.49/0.70  fof(c_0_25, plain, ![X14, X15]:(~v1_relat_1(X14)|v1_relat_1(k7_relat_1(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.49/0.70  fof(c_0_26, plain, ![X27, X28]:(~v1_relat_1(X27)|k2_wellord1(X27,X28)=k3_xboole_0(X27,k2_zfmisc_1(X28,X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).
% 0.49/0.70  cnf(c_0_27, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.49/0.70  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.49/0.70  cnf(c_0_29, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.49/0.70  fof(c_0_30, plain, ![X18, X19]:(~v1_relat_1(X19)|r1_tarski(k2_relat_1(k8_relat_1(X18,X19)),X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).
% 0.49/0.70  cnf(c_0_31, plain, (k2_wellord1(X1,X2)=k8_relat_1(X2,k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.49/0.70  cnf(c_0_32, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.49/0.70  cnf(c_0_33, plain, (k2_wellord1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.49/0.70  fof(c_0_34, plain, ![X20, X21, X22]:(~v1_relat_1(X22)|k7_relat_1(k8_relat_1(X20,X22),X21)=k8_relat_1(X20,k7_relat_1(X22,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).
% 0.49/0.70  fof(c_0_35, plain, ![X16, X17]:(~v1_relat_1(X17)|v1_relat_1(k8_relat_1(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.49/0.70  cnf(c_0_36, negated_conjecture, (r1_tarski(k3_relat_1(X1),k3_relat_1(esk2_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.49/0.70  cnf(c_0_37, negated_conjecture, (v1_relat_1(k3_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.49/0.70  fof(c_0_38, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X8,X7)|r1_tarski(k2_xboole_0(X6,X8),X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.49/0.70  cnf(c_0_39, plain, (r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.49/0.70  cnf(c_0_40, negated_conjecture, (k8_relat_1(X1,k7_relat_1(esk2_0,X1))=k2_wellord1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_28])).
% 0.49/0.70  cnf(c_0_41, negated_conjecture, (v1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_32, c_0_28])).
% 0.49/0.70  fof(c_0_42, plain, ![X13]:(~v1_relat_1(X13)|k3_relat_1(X13)=k2_xboole_0(k1_relat_1(X13),k2_relat_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.49/0.70  cnf(c_0_43, negated_conjecture, (k3_xboole_0(esk2_0,k2_zfmisc_1(X1,X1))=k2_wellord1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_28])).
% 0.49/0.70  fof(c_0_44, plain, ![X25, X26]:(~v1_relat_1(X26)|r1_tarski(k1_relat_1(k7_relat_1(X26,X25)),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.49/0.70  cnf(c_0_45, plain, (k7_relat_1(k8_relat_1(X2,X1),X3)=k8_relat_1(X2,k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.49/0.70  cnf(c_0_46, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.49/0.70  cnf(c_0_47, negated_conjecture, (r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,X1)),k3_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_19]), c_0_37])])).
% 0.49/0.70  cnf(c_0_48, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.49/0.70  cnf(c_0_49, negated_conjecture, (r1_tarski(k2_relat_1(k2_wellord1(esk2_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.49/0.70  cnf(c_0_50, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.49/0.70  cnf(c_0_51, negated_conjecture, (v1_relat_1(k2_wellord1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_43]), c_0_28])])).
% 0.49/0.70  cnf(c_0_52, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.49/0.70  cnf(c_0_53, negated_conjecture, (k7_relat_1(k8_relat_1(X1,esk2_0),X1)=k2_wellord1(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_40]), c_0_28])])).
% 0.49/0.70  cnf(c_0_54, negated_conjecture, (v1_relat_1(k8_relat_1(X1,esk2_0))), inference(spm,[status(thm)],[c_0_46, c_0_28])).
% 0.49/0.70  cnf(c_0_55, negated_conjecture, (~r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),k3_relat_1(esk2_0))|~r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.49/0.70  cnf(c_0_56, negated_conjecture, (r1_tarski(k3_relat_1(k2_wellord1(esk2_0,X1)),k3_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_47, c_0_43])).
% 0.49/0.70  cnf(c_0_57, negated_conjecture, (r1_tarski(k2_xboole_0(X1,k2_relat_1(k2_wellord1(esk2_0,X2))),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.49/0.70  cnf(c_0_58, negated_conjecture, (k2_xboole_0(k1_relat_1(k2_wellord1(esk2_0,X1)),k2_relat_1(k2_wellord1(esk2_0,X1)))=k3_relat_1(k2_wellord1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.49/0.70  cnf(c_0_59, negated_conjecture, (r1_tarski(k1_relat_1(k2_wellord1(esk2_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 0.49/0.70  cnf(c_0_60, negated_conjecture, (~r1_tarski(k3_relat_1(k2_wellord1(esk2_0,esk1_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])])).
% 0.49/0.70  cnf(c_0_61, negated_conjecture, (r1_tarski(k3_relat_1(k2_wellord1(esk2_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.49/0.70  cnf(c_0_62, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61])]), ['proof']).
% 0.49/0.70  # SZS output end CNFRefutation
% 0.49/0.70  # Proof object total steps             : 63
% 0.49/0.70  # Proof object clause steps            : 34
% 0.49/0.70  # Proof object formula steps           : 29
% 0.49/0.70  # Proof object conjectures             : 22
% 0.49/0.70  # Proof object clause conjectures      : 19
% 0.49/0.70  # Proof object formula conjectures     : 3
% 0.49/0.70  # Proof object initial clauses used    : 15
% 0.49/0.70  # Proof object initial formulas used   : 14
% 0.49/0.70  # Proof object generating inferences   : 17
% 0.49/0.70  # Proof object simplifying inferences  : 16
% 0.49/0.70  # Training examples: 0 positive, 0 negative
% 0.49/0.70  # Parsed axioms                        : 14
% 0.49/0.70  # Removed by relevancy pruning/SinE    : 0
% 0.49/0.70  # Initial clauses                      : 16
% 0.49/0.70  # Removed in clause preprocessing      : 0
% 0.49/0.70  # Initial clauses in saturation        : 16
% 0.49/0.70  # Processed clauses                    : 1173
% 0.49/0.70  # ...of these trivial                  : 73
% 0.49/0.70  # ...subsumed                          : 17
% 0.49/0.70  # ...remaining for further processing  : 1083
% 0.49/0.70  # Other redundant clauses eliminated   : 0
% 0.49/0.70  # Clauses deleted for lack of memory   : 0
% 0.49/0.70  # Backward-subsumed                    : 2
% 0.49/0.70  # Backward-rewritten                   : 52
% 0.49/0.70  # Generated clauses                    : 28037
% 0.49/0.70  # ...of the previous two non-trivial   : 27699
% 0.49/0.70  # Contextual simplify-reflections      : 0
% 0.49/0.70  # Paramodulations                      : 28037
% 0.49/0.70  # Factorizations                       : 0
% 0.49/0.70  # Equation resolutions                 : 0
% 0.49/0.70  # Propositional unsat checks           : 0
% 0.49/0.70  #    Propositional check models        : 0
% 0.49/0.70  #    Propositional check unsatisfiable : 0
% 0.49/0.70  #    Propositional clauses             : 0
% 0.49/0.70  #    Propositional clauses after purity: 0
% 0.49/0.70  #    Propositional unsat core size     : 0
% 0.49/0.70  #    Propositional preprocessing time  : 0.000
% 0.49/0.70  #    Propositional encoding time       : 0.000
% 0.49/0.70  #    Propositional solver time         : 0.000
% 0.49/0.70  #    Success case prop preproc time    : 0.000
% 0.49/0.70  #    Success case prop encoding time   : 0.000
% 0.49/0.70  #    Success case prop solver time     : 0.000
% 0.49/0.70  # Current number of processed clauses  : 1013
% 0.49/0.70  #    Positive orientable unit clauses  : 938
% 0.49/0.70  #    Positive unorientable unit clauses: 0
% 0.49/0.70  #    Negative unit clauses             : 0
% 0.49/0.70  #    Non-unit-clauses                  : 75
% 0.49/0.70  # Current number of unprocessed clauses: 26525
% 0.49/0.70  # ...number of literals in the above   : 29052
% 0.49/0.70  # Current number of archived formulas  : 0
% 0.49/0.70  # Current number of archived clauses   : 70
% 0.49/0.70  # Clause-clause subsumption calls (NU) : 458
% 0.49/0.70  # Rec. Clause-clause subsumption calls : 441
% 0.49/0.70  # Non-unit clause-clause subsumptions  : 19
% 0.49/0.70  # Unit Clause-clause subsumption calls : 812
% 0.49/0.70  # Rewrite failures with RHS unbound    : 0
% 0.49/0.70  # BW rewrite match attempts            : 27170
% 0.49/0.70  # BW rewrite match successes           : 46
% 0.49/0.70  # Condensation attempts                : 0
% 0.49/0.70  # Condensation successes               : 0
% 0.49/0.70  # Termbank termtop insertions          : 459078
% 0.49/0.71  
% 0.49/0.71  # -------------------------------------------------
% 0.49/0.71  # User time                : 0.333 s
% 0.49/0.71  # System time              : 0.032 s
% 0.49/0.71  # Total time               : 0.365 s
% 0.49/0.71  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
