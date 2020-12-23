%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:38 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   27 (  54 expanded)
%              Number of clauses        :   16 (  21 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :  119 ( 288 expanded)
%              Number of equality atoms :   35 (  67 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( r2_hidden(X3,k2_relset_1(X1,X2,X4))
          & ! [X5] :
              ~ ( r2_hidden(X5,X1)
                & k1_funct_1(X4,X5) = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ~ ( r2_hidden(X3,k2_relset_1(X1,X2,X4))
            & ! [X5] :
                ~ ( r2_hidden(X5,X1)
                  & k1_funct_1(X4,X5) = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_funct_2])).

fof(c_0_6,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | v1_relat_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_7,negated_conjecture,(
    ! [X32] :
      ( v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk4_0,esk5_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & r2_hidden(esk6_0,k2_relset_1(esk4_0,esk5_0,esk7_0))
      & ( ~ r2_hidden(X32,esk4_0)
        | k1_funct_1(esk7_0,X32) != esk6_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X6,X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(esk1_4(X6,X7,X8,X9),k1_relat_1(X6))
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( X9 = k1_funct_1(X6,esk1_4(X6,X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(X12,k1_relat_1(X6))
        | ~ r2_hidden(X12,X7)
        | X11 != k1_funct_1(X6,X12)
        | r2_hidden(X11,X8)
        | X8 != k9_relat_1(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(esk2_3(X6,X13,X14),X14)
        | ~ r2_hidden(X16,k1_relat_1(X6))
        | ~ r2_hidden(X16,X13)
        | esk2_3(X6,X13,X14) != k1_funct_1(X6,X16)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),k1_relat_1(X6))
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),X13)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( esk2_3(X6,X13,X14) = k1_funct_1(X6,esk3_3(X6,X13,X14))
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k9_relat_1(X6,X13)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

cnf(c_0_9,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | k1_funct_1(esk7_0,X1) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( X1 = k1_funct_1(X2,esk1_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_15,plain,(
    ! [X21,X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | k7_relset_1(X21,X22,X23,X24) = k9_relat_1(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_16,plain,(
    ! [X25,X26,X27] :
      ( ( k7_relset_1(X25,X26,X27,X25) = k2_relset_1(X25,X26,X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( k8_relset_1(X25,X26,X27,X26) = k1_relset_1(X25,X26,X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

cnf(c_0_17,negated_conjecture,
    ( X1 != k9_relat_1(esk7_0,X2)
    | X3 != esk6_0
    | ~ r2_hidden(esk1_4(esk7_0,X2,X1,X3),esk4_0)
    | ~ r2_hidden(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])]),c_0_14])])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( X1 != k9_relat_1(esk7_0,esk4_0)
    | X2 != esk6_0
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_13]),c_0_14])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relset_1(esk4_0,esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,plain,
    ( k2_relset_1(X1,X2,X3) = k9_relat_1(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( X1 != esk6_0
    | ~ r2_hidden(X1,k9_relat_1(esk7_0,esk4_0)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk6_0,k9_relat_1(esk7_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_10])])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.13/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t17_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((r2_hidden(X3,k2_relset_1(X1,X2,X4))&![X5]:~((r2_hidden(X5,X1)&k1_funct_1(X4,X5)=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 0.13/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.37  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 0.13/0.37  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.13/0.37  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((r2_hidden(X3,k2_relset_1(X1,X2,X4))&![X5]:~((r2_hidden(X5,X1)&k1_funct_1(X4,X5)=X3)))))), inference(assume_negation,[status(cth)],[t17_funct_2])).
% 0.13/0.37  fof(c_0_6, plain, ![X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|v1_relat_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.37  fof(c_0_7, negated_conjecture, ![X32]:(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk4_0,esk5_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(r2_hidden(esk6_0,k2_relset_1(esk4_0,esk5_0,esk7_0))&(~r2_hidden(X32,esk4_0)|k1_funct_1(esk7_0,X32)!=esk6_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.13/0.37  fof(c_0_8, plain, ![X6, X7, X8, X9, X11, X12, X13, X14, X16]:(((((r2_hidden(esk1_4(X6,X7,X8,X9),k1_relat_1(X6))|~r2_hidden(X9,X8)|X8!=k9_relat_1(X6,X7)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(r2_hidden(esk1_4(X6,X7,X8,X9),X7)|~r2_hidden(X9,X8)|X8!=k9_relat_1(X6,X7)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(X9=k1_funct_1(X6,esk1_4(X6,X7,X8,X9))|~r2_hidden(X9,X8)|X8!=k9_relat_1(X6,X7)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(~r2_hidden(X12,k1_relat_1(X6))|~r2_hidden(X12,X7)|X11!=k1_funct_1(X6,X12)|r2_hidden(X11,X8)|X8!=k9_relat_1(X6,X7)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&((~r2_hidden(esk2_3(X6,X13,X14),X14)|(~r2_hidden(X16,k1_relat_1(X6))|~r2_hidden(X16,X13)|esk2_3(X6,X13,X14)!=k1_funct_1(X6,X16))|X14=k9_relat_1(X6,X13)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(((r2_hidden(esk3_3(X6,X13,X14),k1_relat_1(X6))|r2_hidden(esk2_3(X6,X13,X14),X14)|X14=k9_relat_1(X6,X13)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(r2_hidden(esk3_3(X6,X13,X14),X13)|r2_hidden(esk2_3(X6,X13,X14),X14)|X14=k9_relat_1(X6,X13)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(esk2_3(X6,X13,X14)=k1_funct_1(X6,esk3_3(X6,X13,X14))|r2_hidden(esk2_3(X6,X13,X14),X14)|X14=k9_relat_1(X6,X13)|(~v1_relat_1(X6)|~v1_funct_1(X6)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.13/0.37  cnf(c_0_9, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (~r2_hidden(X1,esk4_0)|k1_funct_1(esk7_0,X1)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_12, plain, (X1=k1_funct_1(X2,esk1_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_13, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.37  fof(c_0_15, plain, ![X21, X22, X23, X24]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|k7_relset_1(X21,X22,X23,X24)=k9_relat_1(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.13/0.37  fof(c_0_16, plain, ![X25, X26, X27]:((k7_relset_1(X25,X26,X27,X25)=k2_relset_1(X25,X26,X27)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(k8_relset_1(X25,X26,X27,X26)=k1_relset_1(X25,X26,X27)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (X1!=k9_relat_1(esk7_0,X2)|X3!=esk6_0|~r2_hidden(esk1_4(esk7_0,X2,X1,X3),esk4_0)|~r2_hidden(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])]), c_0_14])])).
% 0.13/0.37  cnf(c_0_18, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_19, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_20, plain, (k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (X1!=k9_relat_1(esk7_0,esk4_0)|X2!=esk6_0|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_13]), c_0_14])])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(esk6_0,k2_relset_1(esk4_0,esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_23, plain, (k2_relset_1(X1,X2,X3)=k9_relat_1(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (X1!=esk6_0|~r2_hidden(X1,k9_relat_1(esk7_0,esk4_0))), inference(er,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(esk6_0,k9_relat_1(esk7_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_10])])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 27
% 0.13/0.37  # Proof object clause steps            : 16
% 0.13/0.37  # Proof object formula steps           : 11
% 0.13/0.37  # Proof object conjectures             : 13
% 0.13/0.37  # Proof object clause conjectures      : 10
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 9
% 0.13/0.37  # Proof object initial formulas used   : 5
% 0.13/0.37  # Proof object generating inferences   : 7
% 0.13/0.37  # Proof object simplifying inferences  : 9
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 5
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 17
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 17
% 0.13/0.37  # Processed clauses                    : 40
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 40
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 14
% 0.13/0.37  # ...of the previous two non-trivial   : 13
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 13
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 1
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 23
% 0.13/0.37  #    Positive orientable unit clauses  : 6
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 0
% 0.13/0.37  #    Non-unit-clauses                  : 17
% 0.13/0.37  # Current number of unprocessed clauses: 7
% 0.13/0.37  # ...number of literals in the above   : 51
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 17
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 52
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 7
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 0
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1843
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.030 s
% 0.13/0.37  # System time              : 0.002 s
% 0.13/0.37  # Total time               : 0.032 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
