%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:08 EST 2020

% Result     : Theorem 0.23s
% Output     : CNFRefutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   34 (  47 expanded)
%              Number of clauses        :   17 (  21 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 102 expanded)
%              Number of equality atoms :   29 (  48 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_xboole_0,X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
     => k8_relset_1(k1_xboole_0,X1,X3,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(rc2_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(t172_relat_1,axiom,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_xboole_0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
       => k8_relset_1(k1_xboole_0,X1,X3,X2) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t60_funct_2])).

fof(c_0_9,plain,(
    ! [X37,X38] :
      ( ( k2_zfmisc_1(X37,X38) != k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0 )
      & ( X37 != k1_xboole_0
        | k2_zfmisc_1(X37,X38) = k1_xboole_0 )
      & ( X38 != k1_xboole_0
        | k2_zfmisc_1(X37,X38) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_10,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_11,plain,(
    ! [X39] :
      ( m1_subset_1(esk1_1(X39),k1_zfmisc_1(X39))
      & v1_xboole_0(esk1_1(X39)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).

fof(c_0_12,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))
    & k8_relset_1(k1_xboole_0,esk2_0,esk4_0,esk3_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_13,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v1_xboole_0(esk1_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X42,X43] :
      ( ~ v1_xboole_0(X42)
      | ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | v1_xboole_0(X43) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( esk1_1(X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_15,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_24,negated_conjecture,
    ( k8_relset_1(k1_xboole_0,esk2_0,esk4_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_23])).

fof(c_0_26,plain,(
    ! [X48,X49,X50,X51] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k8_relset_1(X48,X49,X50,X51) = k10_relat_1(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_27,plain,(
    ! [X47] : k10_relat_1(k1_xboole_0,X47) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t172_relat_1])).

fof(c_0_28,plain,(
    ! [X41] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X41)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_29,negated_conjecture,
    ( k8_relset_1(k1_xboole_0,esk2_0,k1_xboole_0,esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_18]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 12:25:45 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  # Version: 2.5pre002
% 0.15/0.37  # No SInE strategy applied
% 0.15/0.37  # Trying AutoSched0 for 299 seconds
% 0.23/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.23/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.23/0.40  #
% 0.23/0.40  # Preprocessing time       : 0.027 s
% 0.23/0.40  # Presaturation interreduction done
% 0.23/0.40  
% 0.23/0.40  # Proof found!
% 0.23/0.40  # SZS status Theorem
% 0.23/0.40  # SZS output start CNFRefutation
% 0.23/0.40  fof(t60_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_xboole_0,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))))=>k8_relset_1(k1_xboole_0,X1,X3,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 0.23/0.40  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.23/0.40  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.23/0.40  fof(rc2_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&v1_xboole_0(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 0.23/0.40  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.23/0.40  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.23/0.40  fof(t172_relat_1, axiom, ![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 0.23/0.40  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.23/0.40  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_xboole_0,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))))=>k8_relset_1(k1_xboole_0,X1,X3,X2)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t60_funct_2])).
% 0.23/0.40  fof(c_0_9, plain, ![X37, X38]:((k2_zfmisc_1(X37,X38)!=k1_xboole_0|(X37=k1_xboole_0|X38=k1_xboole_0))&((X37!=k1_xboole_0|k2_zfmisc_1(X37,X38)=k1_xboole_0)&(X38!=k1_xboole_0|k2_zfmisc_1(X37,X38)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.23/0.40  fof(c_0_10, plain, ![X8]:(~v1_xboole_0(X8)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.23/0.40  fof(c_0_11, plain, ![X39]:(m1_subset_1(esk1_1(X39),k1_zfmisc_1(X39))&v1_xboole_0(esk1_1(X39))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).
% 0.23/0.40  fof(c_0_12, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,k1_xboole_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))))&k8_relset_1(k1_xboole_0,esk2_0,esk4_0,esk3_0)!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.23/0.40  cnf(c_0_13, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.23/0.40  cnf(c_0_14, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.23/0.40  cnf(c_0_15, plain, (v1_xboole_0(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.23/0.40  fof(c_0_16, plain, ![X42, X43]:(~v1_xboole_0(X42)|(~m1_subset_1(X43,k1_zfmisc_1(X42))|v1_xboole_0(X43))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.23/0.40  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.23/0.40  cnf(c_0_18, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_13])).
% 0.23/0.40  cnf(c_0_19, plain, (esk1_1(X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.23/0.40  cnf(c_0_20, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.23/0.40  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.23/0.40  cnf(c_0_22, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_15, c_0_19])).
% 0.23/0.40  cnf(c_0_23, negated_conjecture, (v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.23/0.40  cnf(c_0_24, negated_conjecture, (k8_relset_1(k1_xboole_0,esk2_0,esk4_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.23/0.40  cnf(c_0_25, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_14, c_0_23])).
% 0.23/0.40  fof(c_0_26, plain, ![X48, X49, X50, X51]:(~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|k8_relset_1(X48,X49,X50,X51)=k10_relat_1(X50,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.23/0.40  fof(c_0_27, plain, ![X47]:k10_relat_1(k1_xboole_0,X47)=k1_xboole_0, inference(variable_rename,[status(thm)],[t172_relat_1])).
% 0.23/0.40  fof(c_0_28, plain, ![X41]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X41)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.23/0.40  cnf(c_0_29, negated_conjecture, (k8_relset_1(k1_xboole_0,esk2_0,k1_xboole_0,esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.23/0.40  cnf(c_0_30, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.23/0.40  cnf(c_0_31, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.23/0.40  cnf(c_0_32, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.23/0.40  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_18]), c_0_32])]), ['proof']).
% 0.23/0.40  # SZS output end CNFRefutation
% 0.23/0.40  # Proof object total steps             : 34
% 0.23/0.40  # Proof object clause steps            : 17
% 0.23/0.40  # Proof object formula steps           : 17
% 0.23/0.40  # Proof object conjectures             : 10
% 0.23/0.40  # Proof object clause conjectures      : 7
% 0.23/0.40  # Proof object formula conjectures     : 3
% 0.23/0.40  # Proof object initial clauses used    : 9
% 0.23/0.40  # Proof object initial formulas used   : 8
% 0.23/0.40  # Proof object generating inferences   : 4
% 0.23/0.40  # Proof object simplifying inferences  : 10
% 0.23/0.40  # Training examples: 0 positive, 0 negative
% 0.23/0.40  # Parsed axioms                        : 17
% 0.23/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.23/0.40  # Initial clauses                      : 23
% 0.23/0.40  # Removed in clause preprocessing      : 7
% 0.23/0.40  # Initial clauses in saturation        : 16
% 0.23/0.40  # Processed clauses                    : 42
% 0.23/0.40  # ...of these trivial                  : 1
% 0.23/0.40  # ...subsumed                          : 0
% 0.23/0.40  # ...remaining for further processing  : 41
% 0.23/0.40  # Other redundant clauses eliminated   : 2
% 0.23/0.40  # Clauses deleted for lack of memory   : 0
% 0.23/0.40  # Backward-subsumed                    : 0
% 0.23/0.40  # Backward-rewritten                   : 7
% 0.23/0.40  # Generated clauses                    : 8
% 0.23/0.40  # ...of the previous two non-trivial   : 12
% 0.23/0.40  # Contextual simplify-reflections      : 0
% 0.23/0.40  # Paramodulations                      : 6
% 0.23/0.40  # Factorizations                       : 0
% 0.23/0.40  # Equation resolutions                 : 2
% 0.23/0.40  # Propositional unsat checks           : 0
% 0.23/0.40  #    Propositional check models        : 0
% 0.23/0.40  #    Propositional check unsatisfiable : 0
% 0.23/0.40  #    Propositional clauses             : 0
% 0.23/0.40  #    Propositional clauses after purity: 0
% 0.23/0.40  #    Propositional unsat core size     : 0
% 0.23/0.40  #    Propositional preprocessing time  : 0.000
% 0.23/0.40  #    Propositional encoding time       : 0.000
% 0.23/0.40  #    Propositional solver time         : 0.000
% 0.23/0.40  #    Success case prop preproc time    : 0.000
% 0.23/0.40  #    Success case prop encoding time   : 0.000
% 0.23/0.40  #    Success case prop solver time     : 0.000
% 0.23/0.40  # Current number of processed clauses  : 16
% 0.23/0.40  #    Positive orientable unit clauses  : 10
% 0.23/0.40  #    Positive unorientable unit clauses: 0
% 0.23/0.40  #    Negative unit clauses             : 1
% 0.23/0.40  #    Non-unit-clauses                  : 5
% 0.23/0.40  # Current number of unprocessed clauses: 2
% 0.23/0.40  # ...number of literals in the above   : 4
% 0.23/0.40  # Current number of archived formulas  : 0
% 0.23/0.40  # Current number of archived clauses   : 30
% 0.23/0.40  # Clause-clause subsumption calls (NU) : 4
% 0.23/0.40  # Rec. Clause-clause subsumption calls : 4
% 0.23/0.40  # Non-unit clause-clause subsumptions  : 0
% 0.23/0.40  # Unit Clause-clause subsumption calls : 1
% 0.23/0.40  # Rewrite failures with RHS unbound    : 0
% 0.23/0.40  # BW rewrite match attempts            : 3
% 0.23/0.40  # BW rewrite match successes           : 3
% 0.23/0.40  # Condensation attempts                : 0
% 0.23/0.40  # Condensation successes               : 0
% 0.23/0.40  # Termbank termtop insertions          : 1238
% 0.23/0.40  
% 0.23/0.40  # -------------------------------------------------
% 0.23/0.40  # User time                : 0.028 s
% 0.23/0.40  # System time              : 0.004 s
% 0.23/0.40  # Total time               : 0.032 s
% 0.23/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
