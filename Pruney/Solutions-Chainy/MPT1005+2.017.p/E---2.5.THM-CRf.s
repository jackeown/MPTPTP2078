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
% DateTime   : Thu Dec  3 11:04:04 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   41 (  58 expanded)
%              Number of clauses        :   23 (  28 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 126 expanded)
%              Number of equality atoms :   37 (  43 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(t59_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_xboole_0,X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
     => k7_relset_1(k1_xboole_0,X1,X3,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t34_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_mcart_1(X3,X4,X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_9,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | ~ v1_xboole_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_10,plain,(
    ! [X18,X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | m1_subset_1(k7_relset_1(X18,X19,X20,X21),k1_zfmisc_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_xboole_0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
       => k7_relset_1(k1_xboole_0,X1,X3,X2) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t59_funct_2])).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_16,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,k1_xboole_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk3_0)))
    & k7_relset_1(k1_xboole_0,esk3_0,esk5_0,esk4_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_17,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X22,X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k7_relset_1(X22,X23,X24,X25) = k9_relat_1(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k7_relset_1(X2,X3,k1_xboole_0,X4))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X26,X28,X29,X30,X31] :
      ( ( r2_hidden(esk2_1(X26),X26)
        | X26 = k1_xboole_0 )
      & ( ~ r2_hidden(X28,X26)
        | esk2_1(X26) != k4_mcart_1(X28,X29,X30,X31)
        | X26 = k1_xboole_0 )
      & ( ~ r2_hidden(X29,X26)
        | esk2_1(X26) != k4_mcart_1(X28,X29,X30,X31)
        | X26 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_28,plain,(
    ! [X7] :
      ( X7 = k1_xboole_0
      | r2_hidden(esk1_1(X7),X7) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))
    | ~ v1_xboole_0(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_19])])).

cnf(c_0_30,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_26]),c_0_27])])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k7_relset_1(k1_xboole_0,esk3_0,esk5_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( k7_relset_1(X1,X2,k1_xboole_0,X3) = k9_relat_1(k1_xboole_0,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_19])).

cnf(c_0_37,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( k7_relset_1(k1_xboole_0,esk3_0,k1_xboole_0,esk4_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( k7_relset_1(X1,X2,k1_xboole_0,X3) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:01:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03DN
% 0.12/0.37  # and selection function PSelectComplexExceptRRHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.12/0.37  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 0.12/0.37  fof(t59_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_xboole_0,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))))=>k7_relset_1(k1_xboole_0,X1,X3,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_2)).
% 0.12/0.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.12/0.37  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.12/0.37  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.12/0.37  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 0.12/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.12/0.37  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.12/0.37  fof(c_0_9, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|~v1_xboole_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.12/0.37  fof(c_0_10, plain, ![X18, X19, X20, X21]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|m1_subset_1(k7_relset_1(X18,X19,X20,X21),k1_zfmisc_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 0.12/0.37  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_xboole_0,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))))=>k7_relset_1(k1_xboole_0,X1,X3,X2)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t59_funct_2])).
% 0.12/0.37  fof(c_0_12, plain, ![X9, X10]:((k2_zfmisc_1(X9,X10)!=k1_xboole_0|(X9=k1_xboole_0|X10=k1_xboole_0))&((X9!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0)&(X10!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.12/0.37  cnf(c_0_13, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_14, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  fof(c_0_15, plain, ![X11]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.12/0.37  fof(c_0_16, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,k1_xboole_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk3_0))))&k7_relset_1(k1_xboole_0,esk3_0,esk5_0,esk4_0)!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.12/0.37  cnf(c_0_17, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_18, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.37  cnf(c_0_19, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  fof(c_0_20, plain, ![X22, X23, X24, X25]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|k7_relset_1(X22,X23,X24,X25)=k9_relat_1(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_22, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_23, plain, (~r2_hidden(X1,k7_relset_1(X2,X3,k1_xboole_0,X4))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_24, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  fof(c_0_25, plain, ![X26, X28, X29, X30, X31]:((r2_hidden(esk2_1(X26),X26)|X26=k1_xboole_0)&((~r2_hidden(X28,X26)|esk2_1(X26)!=k4_mcart_1(X28,X29,X30,X31)|X26=k1_xboole_0)&(~r2_hidden(X29,X26)|esk2_1(X26)!=k4_mcart_1(X28,X29,X30,X31)|X26=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.37  cnf(c_0_27, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.12/0.37  fof(c_0_28, plain, ![X7]:(X7=k1_xboole_0|r2_hidden(esk1_1(X7),X7)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.12/0.37  cnf(c_0_29, plain, (~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))|~v1_xboole_0(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_19])])).
% 0.12/0.37  cnf(c_0_30, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_26]), c_0_27])])).
% 0.12/0.37  cnf(c_0_32, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_33, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (k7_relset_1(k1_xboole_0,esk3_0,esk5_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.37  cnf(c_0_36, plain, (k7_relset_1(X1,X2,k1_xboole_0,X3)=k9_relat_1(k1_xboole_0,X3)), inference(spm,[status(thm)],[c_0_24, c_0_19])).
% 0.12/0.37  cnf(c_0_37, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_27])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (k7_relset_1(k1_xboole_0,esk3_0,k1_xboole_0,esk4_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.12/0.37  cnf(c_0_39, plain, (k7_relset_1(X1,X2,k1_xboole_0,X3)=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 41
% 0.12/0.37  # Proof object clause steps            : 23
% 0.12/0.37  # Proof object formula steps           : 18
% 0.12/0.37  # Proof object conjectures             : 10
% 0.12/0.37  # Proof object clause conjectures      : 7
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 10
% 0.12/0.37  # Proof object initial formulas used   : 9
% 0.12/0.37  # Proof object generating inferences   : 8
% 0.12/0.37  # Proof object simplifying inferences  : 10
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 10
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 17
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 17
% 0.12/0.37  # Processed clauses                    : 59
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 6
% 0.12/0.37  # ...remaining for further processing  : 53
% 0.12/0.37  # Other redundant clauses eliminated   : 4
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 2
% 0.12/0.37  # Backward-rewritten                   : 10
% 0.12/0.37  # Generated clauses                    : 47
% 0.12/0.37  # ...of the previous two non-trivial   : 47
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 35
% 0.12/0.37  # Factorizations                       : 8
% 0.12/0.37  # Equation resolutions                 : 4
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 22
% 0.12/0.37  #    Positive orientable unit clauses  : 9
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 12
% 0.12/0.37  # Current number of unprocessed clauses: 21
% 0.12/0.37  # ...number of literals in the above   : 42
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 29
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 36
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 31
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 5
% 0.12/0.37  # Unit Clause-clause subsumption calls : 5
% 0.12/0.37  # Rewrite failures with RHS unbound    : 6
% 0.12/0.37  # BW rewrite match attempts            : 12
% 0.12/0.37  # BW rewrite match successes           : 8
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1591
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.030 s
% 0.12/0.37  # System time              : 0.003 s
% 0.12/0.37  # Total time               : 0.033 s
% 0.12/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
