%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:08 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 106 expanded)
%              Number of clauses        :   33 (  52 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  130 ( 277 expanded)
%              Number of equality atoms :   29 (  87 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t60_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_xboole_0,X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
     => k8_relset_1(k1_xboole_0,X1,X3,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t47_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r1_tarski(k8_relset_1(X1,X2,X4,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_2)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(c_0_12,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X13,X12)
        | r2_hidden(X13,X12)
        | v1_xboole_0(X12) )
      & ( ~ r2_hidden(X13,X12)
        | m1_subset_1(X13,X12)
        | v1_xboole_0(X12) )
      & ( ~ m1_subset_1(X13,X12)
        | v1_xboole_0(X13)
        | ~ v1_xboole_0(X12) )
      & ( ~ v1_xboole_0(X13)
        | m1_subset_1(X13,X12)
        | ~ v1_xboole_0(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_13,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_14,plain,(
    ! [X10,X11] :
      ( ( k2_zfmisc_1(X10,X11) != k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_xboole_0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
       => k8_relset_1(k1_xboole_0,X1,X3,X2) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t60_funct_2])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_xboole_0(X18)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X19,X18)))
      | v1_xboole_0(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_19,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))
    & k8_relset_1(k1_xboole_0,esk2_0,esk4_0,esk3_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_21,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_24,plain,(
    ! [X14] : ~ v1_xboole_0(k1_zfmisc_1(X14)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X21,X22,X23,X24] :
      ( ~ v1_funct_1(X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | r1_tarski(k8_relset_1(X21,X22,X24,X23),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_2])])).

cnf(c_0_38,plain,
    ( v1_xboole_0(esk1_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_xboole_0(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_31]),c_0_32])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_42,plain,
    ( r1_tarski(k8_relset_1(X2,X3,X1,X4),X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_43,plain,(
    ! [X17] :
      ( v1_relat_1(k6_relat_1(X17))
      & v1_funct_1(k6_relat_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_44,plain,
    ( v1_xboole_0(esk1_1(k1_zfmisc_1(k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_26]),c_0_27])])).

cnf(c_0_45,negated_conjecture,
    ( k8_relset_1(k1_xboole_0,esk2_0,esk4_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k8_relset_1(k1_xboole_0,X1,X2,X3))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_29])).

cnf(c_0_48,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_50,plain,
    ( esk1_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k8_relset_1(k1_xboole_0,esk2_0,k1_xboole_0,esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( k8_relset_1(k1_xboole_0,X1,X2,X3) = k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_47])).

cnf(c_0_53,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_50]),c_0_32])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:53:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S060N
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.37  fof(t60_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_xboole_0,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))))=>k8_relset_1(k1_xboole_0,X1,X3,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 0.19/0.37  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.19/0.37  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.19/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.37  fof(t47_funct_2, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k8_relset_1(X1,X2,X4,X3),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_2)).
% 0.19/0.37  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.19/0.37  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.19/0.37  fof(c_0_12, plain, ![X12, X13]:(((~m1_subset_1(X13,X12)|r2_hidden(X13,X12)|v1_xboole_0(X12))&(~r2_hidden(X13,X12)|m1_subset_1(X13,X12)|v1_xboole_0(X12)))&((~m1_subset_1(X13,X12)|v1_xboole_0(X13)|~v1_xboole_0(X12))&(~v1_xboole_0(X13)|m1_subset_1(X13,X12)|~v1_xboole_0(X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.37  fof(c_0_13, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.37  fof(c_0_14, plain, ![X10, X11]:((k2_zfmisc_1(X10,X11)!=k1_xboole_0|(X10=k1_xboole_0|X11=k1_xboole_0))&((X10!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0)&(X11!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.37  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_xboole_0,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))))=>k8_relset_1(k1_xboole_0,X1,X3,X2)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t60_funct_2])).
% 0.19/0.37  cnf(c_0_16, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_17, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  fof(c_0_18, plain, ![X18, X19, X20]:(~v1_xboole_0(X18)|(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X19,X18)))|v1_xboole_0(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.19/0.37  cnf(c_0_19, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  fof(c_0_20, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,k1_xboole_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))))&k8_relset_1(k1_xboole_0,esk2_0,esk4_0,esk3_0)!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.19/0.37  cnf(c_0_21, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_22, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.37  cnf(c_0_23, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  fof(c_0_24, plain, ![X14]:~v1_xboole_0(k1_zfmisc_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.19/0.37  cnf(c_0_25, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_26, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_27, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  cnf(c_0_29, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.37  fof(c_0_30, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.37  cnf(c_0_31, plain, (m1_subset_1(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.37  cnf(c_0_32, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  fof(c_0_33, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.37  cnf(c_0_34, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.37  cnf(c_0_36, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.37  fof(c_0_37, plain, ![X21, X22, X23, X24]:(~v1_funct_1(X24)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|r1_tarski(k8_relset_1(X21,X22,X24,X23),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_2])])).
% 0.19/0.37  cnf(c_0_38, plain, (v1_xboole_0(esk1_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))|~v1_xboole_0(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_31]), c_0_32])).
% 0.19/0.37  cnf(c_0_39, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.37  cnf(c_0_41, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_36])).
% 0.19/0.37  cnf(c_0_42, plain, (r1_tarski(k8_relset_1(X2,X3,X1,X4),X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.37  fof(c_0_43, plain, ![X17]:(v1_relat_1(k6_relat_1(X17))&v1_funct_1(k6_relat_1(X17))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.19/0.37  cnf(c_0_44, plain, (v1_xboole_0(esk1_1(k1_zfmisc_1(k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_26]), c_0_27])])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (k8_relset_1(k1_xboole_0,esk2_0,esk4_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.37  cnf(c_0_47, plain, (v1_xboole_0(k8_relset_1(k1_xboole_0,X1,X2,X3))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_29])).
% 0.19/0.37  cnf(c_0_48, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.37  cnf(c_0_49, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.19/0.37  cnf(c_0_50, plain, (esk1_1(k1_zfmisc_1(k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_44])).
% 0.19/0.37  cnf(c_0_51, negated_conjecture, (k8_relset_1(k1_xboole_0,esk2_0,k1_xboole_0,esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.37  cnf(c_0_52, plain, (k8_relset_1(k1_xboole_0,X1,X2,X3)=k1_xboole_0|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_39, c_0_47])).
% 0.19/0.37  cnf(c_0_53, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.37  cnf(c_0_54, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_50]), c_0_32])).
% 0.19/0.37  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 56
% 0.19/0.37  # Proof object clause steps            : 33
% 0.19/0.37  # Proof object formula steps           : 23
% 0.19/0.37  # Proof object conjectures             : 10
% 0.19/0.37  # Proof object clause conjectures      : 7
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 15
% 0.19/0.37  # Proof object initial formulas used   : 12
% 0.19/0.37  # Proof object generating inferences   : 13
% 0.19/0.37  # Proof object simplifying inferences  : 15
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 12
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 23
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 23
% 0.19/0.37  # Processed clauses                    : 86
% 0.19/0.37  # ...of these trivial                  : 2
% 0.19/0.37  # ...subsumed                          : 11
% 0.19/0.37  # ...remaining for further processing  : 73
% 0.19/0.37  # Other redundant clauses eliminated   : 2
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 8
% 0.19/0.37  # Generated clauses                    : 67
% 0.19/0.37  # ...of the previous two non-trivial   : 41
% 0.19/0.37  # Contextual simplify-reflections      : 1
% 0.19/0.37  # Paramodulations                      : 65
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 2
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 40
% 0.19/0.37  #    Positive orientable unit clauses  : 15
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 2
% 0.19/0.37  #    Non-unit-clauses                  : 23
% 0.19/0.37  # Current number of unprocessed clauses: 1
% 0.19/0.37  # ...number of literals in the above   : 4
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 31
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 60
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 48
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 7
% 0.19/0.37  # Unit Clause-clause subsumption calls : 0
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 4
% 0.19/0.37  # BW rewrite match successes           : 3
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1983
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.031 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.035 s
% 0.19/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
