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
% DateTime   : Thu Dec  3 11:06:29 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   40 (  93 expanded)
%              Number of clauses        :   23 (  37 expanded)
%              Number of leaves         :    8 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  140 ( 401 expanded)
%              Number of equality atoms :   17 (  44 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t115_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ~ ( r2_hidden(X6,X1)
                  & r2_hidden(X6,X3)
                  & X5 = k1_funct_1(X4,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ~ ( r2_hidden(X6,X1)
                    & r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t115_funct_2])).

fof(c_0_9,plain,(
    ! [X23,X24,X25] :
      ( ( v4_relat_1(X25,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( v5_relat_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_10,negated_conjecture,(
    ! [X35] :
      ( v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,esk2_0,esk3_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & r2_hidden(esk6_0,k7_relset_1(esk2_0,esk3_0,esk5_0,esk4_0))
      & ( ~ r2_hidden(X35,esk2_0)
        | ~ r2_hidden(X35,esk4_0)
        | esk6_0 != k1_funct_1(esk5_0,X35) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | v1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_12,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | ~ v4_relat_1(X13,X12)
      | X13 = k7_relat_1(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_13,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X14,X15,X16] :
      ( ( r2_hidden(X14,X15)
        | ~ r2_hidden(X14,k1_relat_1(k7_relat_1(X16,X15)))
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(X14,k1_relat_1(X16))
        | ~ r2_hidden(X14,k1_relat_1(k7_relat_1(X16,X15)))
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(X14,X15)
        | ~ r2_hidden(X14,k1_relat_1(X16))
        | r2_hidden(X14,k1_relat_1(k7_relat_1(X16,X15)))
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_17,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v4_relat_1(esk5_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

fof(c_0_20,plain,(
    ! [X17,X18,X19] :
      ( ( r2_hidden(X17,k1_relat_1(X19))
        | ~ r2_hidden(k4_tarski(X17,X18),X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( X18 = k1_funct_1(X19,X17)
        | ~ r2_hidden(k4_tarski(X17,X18),X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( ~ r2_hidden(X17,k1_relat_1(X19))
        | X18 != k1_funct_1(X19,X17)
        | r2_hidden(k4_tarski(X17,X18),X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_21,plain,(
    ! [X7,X8,X9,X11] :
      ( ( r2_hidden(esk1_3(X7,X8,X9),k1_relat_1(X9))
        | ~ r2_hidden(X7,k9_relat_1(X9,X8))
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(k4_tarski(esk1_3(X7,X8,X9),X7),X9)
        | ~ r2_hidden(X7,k9_relat_1(X9,X8))
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(esk1_3(X7,X8,X9),X8)
        | ~ r2_hidden(X7,k9_relat_1(X9,X8))
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(X11,k1_relat_1(X9))
        | ~ r2_hidden(k4_tarski(X11,X7),X9)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X7,k9_relat_1(X9,X8))
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k7_relat_1(esk5_0,esk2_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

fof(c_0_24,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k7_relset_1(X26,X27,X28,X29) = k9_relat_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_25,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_19])])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk4_0)
    | esk6_0 != k1_funct_1(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,plain,
    ( k1_funct_1(X1,esk1_3(X2,X3,X1)) = X2
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,esk5_0),esk2_0)
    | ~ r2_hidden(X1,k9_relat_1(esk5_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_19])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk6_0,k7_relset_1(esk2_0,esk3_0,esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( k7_relset_1(esk2_0,esk3_0,esk5_0,X1) = k9_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk6_0,X1,esk5_0),esk4_0)
    | ~ r2_hidden(esk6_0,k9_relat_1(esk5_0,X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_19])])]),c_0_33])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk6_0,k9_relat_1(esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.32  % CPULimit   : 60
% 0.17/0.32  % WCLimit    : 600
% 0.17/0.32  % DateTime   : Tue Dec  1 19:36:59 EST 2020
% 0.17/0.32  % CPUTime    : 
% 0.17/0.32  # Version: 2.5pre002
% 0.17/0.32  # No SInE strategy applied
% 0.17/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.17/0.35  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.17/0.35  #
% 0.17/0.35  # Preprocessing time       : 0.028 s
% 0.17/0.35  # Presaturation interreduction done
% 0.17/0.35  
% 0.17/0.35  # Proof found!
% 0.17/0.35  # SZS status Theorem
% 0.17/0.35  # SZS output start CNFRefutation
% 0.17/0.35  fof(t115_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 0.17/0.35  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.17/0.35  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.17/0.35  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.17/0.35  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 0.17/0.35  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.17/0.35  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.17/0.35  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.17/0.35  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))))))), inference(assume_negation,[status(cth)],[t115_funct_2])).
% 0.17/0.35  fof(c_0_9, plain, ![X23, X24, X25]:((v4_relat_1(X25,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(v5_relat_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.17/0.35  fof(c_0_10, negated_conjecture, ![X35]:(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(r2_hidden(esk6_0,k7_relset_1(esk2_0,esk3_0,esk5_0,esk4_0))&(~r2_hidden(X35,esk2_0)|~r2_hidden(X35,esk4_0)|esk6_0!=k1_funct_1(esk5_0,X35)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.17/0.35  fof(c_0_11, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|v1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.17/0.35  fof(c_0_12, plain, ![X12, X13]:(~v1_relat_1(X13)|~v4_relat_1(X13,X12)|X13=k7_relat_1(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.17/0.35  cnf(c_0_13, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.17/0.35  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.35  cnf(c_0_15, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.35  fof(c_0_16, plain, ![X14, X15, X16]:(((r2_hidden(X14,X15)|~r2_hidden(X14,k1_relat_1(k7_relat_1(X16,X15)))|~v1_relat_1(X16))&(r2_hidden(X14,k1_relat_1(X16))|~r2_hidden(X14,k1_relat_1(k7_relat_1(X16,X15)))|~v1_relat_1(X16)))&(~r2_hidden(X14,X15)|~r2_hidden(X14,k1_relat_1(X16))|r2_hidden(X14,k1_relat_1(k7_relat_1(X16,X15)))|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.17/0.35  cnf(c_0_17, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.35  cnf(c_0_18, negated_conjecture, (v4_relat_1(esk5_0,esk2_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.17/0.35  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_15, c_0_14])).
% 0.17/0.35  fof(c_0_20, plain, ![X17, X18, X19]:(((r2_hidden(X17,k1_relat_1(X19))|~r2_hidden(k4_tarski(X17,X18),X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(X18=k1_funct_1(X19,X17)|~r2_hidden(k4_tarski(X17,X18),X19)|(~v1_relat_1(X19)|~v1_funct_1(X19))))&(~r2_hidden(X17,k1_relat_1(X19))|X18!=k1_funct_1(X19,X17)|r2_hidden(k4_tarski(X17,X18),X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.17/0.35  fof(c_0_21, plain, ![X7, X8, X9, X11]:((((r2_hidden(esk1_3(X7,X8,X9),k1_relat_1(X9))|~r2_hidden(X7,k9_relat_1(X9,X8))|~v1_relat_1(X9))&(r2_hidden(k4_tarski(esk1_3(X7,X8,X9),X7),X9)|~r2_hidden(X7,k9_relat_1(X9,X8))|~v1_relat_1(X9)))&(r2_hidden(esk1_3(X7,X8,X9),X8)|~r2_hidden(X7,k9_relat_1(X9,X8))|~v1_relat_1(X9)))&(~r2_hidden(X11,k1_relat_1(X9))|~r2_hidden(k4_tarski(X11,X7),X9)|~r2_hidden(X11,X8)|r2_hidden(X7,k9_relat_1(X9,X8))|~v1_relat_1(X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.17/0.35  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.17/0.35  cnf(c_0_23, negated_conjecture, (k7_relat_1(esk5_0,esk2_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.17/0.35  fof(c_0_24, plain, ![X26, X27, X28, X29]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k7_relset_1(X26,X27,X28,X29)=k9_relat_1(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.17/0.35  cnf(c_0_25, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.35  cnf(c_0_26, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.17/0.35  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,esk2_0)|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_19])])).
% 0.17/0.35  cnf(c_0_28, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.17/0.35  cnf(c_0_29, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.17/0.35  cnf(c_0_30, negated_conjecture, (~r2_hidden(X1,esk2_0)|~r2_hidden(X1,esk4_0)|esk6_0!=k1_funct_1(esk5_0,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.35  cnf(c_0_31, plain, (k1_funct_1(X1,esk1_3(X2,X3,X1))=X2|~v1_funct_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.17/0.35  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.35  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_3(X1,X2,esk5_0),esk2_0)|~r2_hidden(X1,k9_relat_1(esk5_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_19])])).
% 0.17/0.35  cnf(c_0_34, negated_conjecture, (r2_hidden(esk6_0,k7_relset_1(esk2_0,esk3_0,esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.35  cnf(c_0_35, negated_conjecture, (k7_relset_1(esk2_0,esk3_0,esk5_0,X1)=k9_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_14])).
% 0.17/0.35  cnf(c_0_36, negated_conjecture, (~r2_hidden(esk1_3(esk6_0,X1,esk5_0),esk4_0)|~r2_hidden(esk6_0,k9_relat_1(esk5_0,X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_19])])]), c_0_33])).
% 0.17/0.35  cnf(c_0_37, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.17/0.35  cnf(c_0_38, negated_conjecture, (r2_hidden(esk6_0,k9_relat_1(esk5_0,esk4_0))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.17/0.35  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_19])]), ['proof']).
% 0.17/0.35  # SZS output end CNFRefutation
% 0.17/0.35  # Proof object total steps             : 40
% 0.17/0.35  # Proof object clause steps            : 23
% 0.17/0.35  # Proof object formula steps           : 17
% 0.17/0.35  # Proof object conjectures             : 16
% 0.17/0.35  # Proof object clause conjectures      : 13
% 0.17/0.35  # Proof object formula conjectures     : 3
% 0.17/0.35  # Proof object initial clauses used    : 13
% 0.17/0.35  # Proof object initial formulas used   : 8
% 0.17/0.35  # Proof object generating inferences   : 9
% 0.17/0.35  # Proof object simplifying inferences  : 15
% 0.17/0.35  # Training examples: 0 positive, 0 negative
% 0.17/0.35  # Parsed axioms                        : 8
% 0.17/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.35  # Initial clauses                      : 20
% 0.17/0.35  # Removed in clause preprocessing      : 0
% 0.17/0.35  # Initial clauses in saturation        : 20
% 0.17/0.35  # Processed clauses                    : 52
% 0.17/0.35  # ...of these trivial                  : 0
% 0.17/0.35  # ...subsumed                          : 0
% 0.17/0.35  # ...remaining for further processing  : 52
% 0.17/0.35  # Other redundant clauses eliminated   : 2
% 0.17/0.35  # Clauses deleted for lack of memory   : 0
% 0.17/0.35  # Backward-subsumed                    : 0
% 0.17/0.35  # Backward-rewritten                   : 1
% 0.17/0.35  # Generated clauses                    : 35
% 0.17/0.35  # ...of the previous two non-trivial   : 29
% 0.17/0.35  # Contextual simplify-reflections      : 1
% 0.17/0.35  # Paramodulations                      : 33
% 0.17/0.35  # Factorizations                       : 0
% 0.17/0.35  # Equation resolutions                 : 2
% 0.17/0.35  # Propositional unsat checks           : 0
% 0.17/0.35  #    Propositional check models        : 0
% 0.17/0.35  #    Propositional check unsatisfiable : 0
% 0.17/0.35  #    Propositional clauses             : 0
% 0.17/0.35  #    Propositional clauses after purity: 0
% 0.17/0.35  #    Propositional unsat core size     : 0
% 0.17/0.35  #    Propositional preprocessing time  : 0.000
% 0.17/0.35  #    Propositional encoding time       : 0.000
% 0.17/0.35  #    Propositional solver time         : 0.000
% 0.17/0.35  #    Success case prop preproc time    : 0.000
% 0.17/0.35  #    Success case prop encoding time   : 0.000
% 0.17/0.35  #    Success case prop solver time     : 0.000
% 0.17/0.35  # Current number of processed clauses  : 30
% 0.17/0.35  #    Positive orientable unit clauses  : 9
% 0.17/0.35  #    Positive unorientable unit clauses: 0
% 0.17/0.35  #    Negative unit clauses             : 0
% 0.17/0.35  #    Non-unit-clauses                  : 21
% 0.17/0.35  # Current number of unprocessed clauses: 17
% 0.17/0.35  # ...number of literals in the above   : 79
% 0.17/0.35  # Current number of archived formulas  : 0
% 0.17/0.35  # Current number of archived clauses   : 21
% 0.17/0.35  # Clause-clause subsumption calls (NU) : 122
% 0.17/0.35  # Rec. Clause-clause subsumption calls : 60
% 0.17/0.35  # Non-unit clause-clause subsumptions  : 1
% 0.17/0.35  # Unit Clause-clause subsumption calls : 0
% 0.17/0.35  # Rewrite failures with RHS unbound    : 0
% 0.17/0.35  # BW rewrite match attempts            : 1
% 0.17/0.35  # BW rewrite match successes           : 1
% 0.17/0.35  # Condensation attempts                : 0
% 0.17/0.35  # Condensation successes               : 0
% 0.17/0.35  # Termbank termtop insertions          : 2348
% 0.17/0.35  
% 0.17/0.35  # -------------------------------------------------
% 0.17/0.35  # User time                : 0.029 s
% 0.17/0.35  # System time              : 0.005 s
% 0.17/0.35  # Total time               : 0.035 s
% 0.17/0.35  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
